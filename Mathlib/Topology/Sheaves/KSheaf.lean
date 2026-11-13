/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-!
# K-sheaves

We define K-sheaves on `X` a T2 topological space with value in an arbitrary category `A`.

This coresponds to the presheaves `F : (Compacts X)ᵒᵖ ⥤ A` such that:
- `F.obj (∅)` is terminal.
- For any two compacts subsets `K₁` and `K₂` of `X`, `F.obj (K₁ ∪ K₂)` is the pullback
  of `F.obj K₁` and `F.obj K₂` over `F.obj (K₁ ∩ K₂)`.
- For any compact subset `K` of `X`, `F.obj K` is the colimit of the `F.obj L` for all the compacts
  subsets `L` of `X` such that `K` is in the interior of `L`.

The category of K-sheaves is a topos, because it is equivalent to the category of sheaves over `X`
(TODO Yannis Monbru Carcelero), but the condition that `K`-presheaves need to verify to
be `K`-sheaves is *not* expressed as the sheaf condition for a Grothendieck topology on
compact sets. Indeed, two of three conditions do involve limits, but the third
`nonempty_isColimit_coconeOfCompact` involves colimits.

## References

*[J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli
spaces of pseudo-holomorphic curves*, Section A.1][Pardon2016]
*[Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

variable (A X) in
/-- The category of `A`-valued K-presheaves on a (bundled) topological space `X` -/
abbrev KPresheaf : Type max u v w := (Compacts X)ᵒᵖ ⥤ A

namespace KPresheaf

/-- If `P` is a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op L)` for `L` a compact
neighbourhood of `K` -/
@[simps, implicit_reducible]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Set.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map <| opHomOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)
  ι.naturality _ _ _ := by
    dsimp
    rw [← P.map_comp, Category.comp_id]
    rfl

/-- For `P` a K-presheaf, and `K` a compact subset then `P.obj (op K)` is equipped with a
structure of cocone over the diagram defined by the `P.obj (op (closure (U : Set X))`
for `U` an open neighbourhood of `K` -/
@[simps!, implicit_reducible]
def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X) :=
  Cocone.whisker K.openRcNhdsToCompactNhds_mono.functor.op <| P.coconeOfCompacts K

variable [T2Space X]

/-- For `K` a compact and `P` a K-presheaf verifying the third axiom of K-sheaves, this is
a recipe to build maps from `P.obj (op K)` by only using the open relatively
compact neighbourhoods and not all the compacts neighbourhoods. -/
@[no_expose]
noncomputable def descOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    P.obj (op K) ⟶ Z :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).desc (Cocone.mk _ ι)

@[reassoc (attr := simp)]
lemma map_comp_descOfOpenClosure (P : KPresheaf A X) {K : Compacts X} (V : K.openRcNhds)
    (h : (IsColimit (P.coconeOfCompacts K))) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P ⟶
      (Functor.const _).obj Z) :
    dsimp% P.map (op (homOfLE (V.property.2.trans subset_closure))) ≫ P.descOfOpenClosure K h ι =
      ι.app (op V) :=
  ((Functor.Final.isColimitWhiskerEquiv
    K.openRcNhdsToCompactNhds_mono.functor.op _).symm h).fac (Cocone.mk _ ι) (op V)

@[ext]
lemma hom_ext_of_isColimit_coconeOfCompacts (P : KPresheaf A X) {K : Compacts X}
    (h : IsColimit (P.coconeOfCompacts K))
    {W : A} {f f' : P.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.coconeOfClosureOfOpens K).ι.app V ≫ f =
      (P.coconeOfClosureOfOpens K).ι.app V ≫ f') :
    f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv K.openRcNhdsToCompactNhds_mono.functor.op
    _).symm h).hom_ext w

/-- The K-sheaf condition. It's a generalisation of the one of J.Pardon (definition A.1.4) that
  correspond to the one of J.Lurie (definition 7.3.4.1) in the case of usual categories.
-/
structure IsKSheaf (P : KPresheaf A X) : Prop where
  nonempty_isTerminal : Nonempty (IsTerminal (P.obj (op ⊥)))
  isPullback {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.map <| opHomOfLE h.le₂₄) (P.map <| opHomOfLE h.le₃₄)
      (P.map <| opHomOfLE h.le₁₂) (P.map <| opHomOfLE h.le₁₃)
  nonempty_isColimit_coconeOfCompacts (K : Compacts X) :
      Nonempty (IsColimit (P.coconeOfCompacts K))

end KPresheaf

variable [T2Space X]

variable (A X) in
/-- The object property of being a K-sheaf -/
abbrev KPresheaf.isKSheaf : ObjectProperty (KPresheaf A X) := IsKSheaf

variable (A X) in
/-- The category of K-sheaves taking values in `A` on a T2-Space. -/
abbrev KSheaf := (KPresheaf.isKSheaf A X).FullSubcategory

instance : (KPresheaf.isKSheaf A X).IsClosedUnderIsomorphisms where
  of_iso e h :=
    { nonempty_isTerminal := ⟨h.nonempty_isTerminal.some.ofIso (e.app _)⟩
      isPullback sq :=
        (h.isPullback sq).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
          (by cat_disch)  (by cat_disch) (by cat_disch) (by cat_disch)
      nonempty_isColimit_coconeOfCompacts K :=
        ⟨(IsColimit.equivOfNatIsoOfIso (Functor.isoWhiskerLeft _ e) _ _
            (by exact Cocone.ext (e.app _)))
          (h.nonempty_isColimit_coconeOfCompacts K).some⟩ }

variable {J K : Type*} [Category* J] [Category* K]
variable {C : Type*} [Category* C]
variable (F : J ⥤ K ⥤ C) (D : DiagramOfCones F) (Df : DiagramOfCones F.flip)

variable (Q : ∀ j, IsLimit (D.obj j)) (c : Cone D.conePoints) (hc : IsLimit c)
variable (Qf : ∀ k, IsLimit (Df.obj k)) (cf : Cone Df.conePoints) (hcf : IsLimit cf)

def truc : c.pt ≅ cf.pt := by


  sorry



instance [HasLimitsOfSize.{w,w} A] [HasLimitsOfSize.{0,0} A] : (KPresheaf.isKSheaf A X).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    {
      limitsOfShape_le := by
        intro F ⟨⟨diag,π,isLimit⟩ ,h⟩
        exact {
          nonempty_isTerminal := by
            apply Nonempty.intro
            have j : J := by sorry

            --have D : J ⥤ _ ⥤ A := (Functor.const J).obj (Functor.empty A)
            #check CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim

            #check diag.flip.obj (op ⊥)
            #check dsimp% (h j).nonempty_isTerminal.some

            let D : DiagramOfCones <| (Functor.const J).obj (Functor.empty A) :=
              {
                obj j := asEmptyCone <| (diag.obj j).obj (op ⊥ )
                map {j j'} f:= {
                  hom := IsTerminal.from (h j').nonempty_isTerminal.some _
                  }
              }

            let l := coneOfConeUncurryIsLimit (D := D) (Q := fun j => (h j).nonempty_isTerminal.some) (c := {
                  pt := (F.obj (op ⊥))
                  π := {
                    app x:= PEmpty.elim x.2.1
                  }
                  })
            unfold coneOfConeUncurry  Functor.uncurry at l
            simp at l
            exact l





            sorry
          isPullback sq := by

            sorry
          nonempty_isColimit_coconeOfCompacts := sorry
        }
    }

namespace KSheaf

/-- If `P` is a K-sheaf, this is the evidence that for any `K` a compact subset of `X`,
 `P.obj.coconeOfCompacts K` is a colimit cocone
-/
@[no_expose]
noncomputable def isColimit (P : KSheaf A X) (K : Compacts X) :
    IsColimit (P.obj.coconeOfCompacts K) :=
  (P.property.nonempty_isColimit_coconeOfCompacts K).some

/-- For `K` a compact and `P` a K-sheaf, this is a recipe to build maps from
`P.obj (op K)` by only using the open relatively compact neighbourhoods and not
all the compacts neighbourhoods. -/
noncomputable def descOfOpenClosure (P : KSheaf A X) (K : Compacts X) {Z : A}
    (ι : K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P.obj ⟶
      (Functor.const _).obj Z) :
    P.obj.obj (op K) ⟶ Z := P.obj.descOfOpenClosure K (P.isColimit K) ι

@[ext]
lemma hom_ext_of_compacts (P : KSheaf A X) {K : Compacts X} {W : A} {f f' : P.obj.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f =
    (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f') : f = f' :=
  KPresheaf.hom_ext_of_isColimit_coconeOfCompacts _ (P.isColimit K) w

end KSheaf

end TopCat
