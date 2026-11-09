/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.Topology.Sheaves.KPresheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!
# K-sheaves

We define K-sheaves on `X` a T2 topological space with value in an arbitrary category `A`.

This corespond to the  `F : (Compacts X)ᵒᵖ ⥤ A` such that:
- `F.obj (∅)`  is terminal.
- For any two compacts subsets `K₁` and  `K₂` of `X`, `F.obj (K₁ ∪ K₂)` is obtained by
  gluing `F.obj K₁` and `F.obj K₂` over `F.obj K₁ ∩ K₂`.
- For any compact subset `K` of `X`, `F.obj K` is the colimit of the `F.obj L` for all the compacts
  subsets `L` of `X`such that `K` is in the interior of `L`.

One may expect this notion to come from sheaves on a site of compact subset of a topological space
but there is no corresponding Grothendieck topology on compact subsets, in particular
because the `nonempty_isColimit_coconeOfCompacts` condition can't be expressed as a sheaf condition.

However this category turns out to be equivalent to the category of sheaves over `X`,
and is thus a topos.

TODO: provide the equivalence of category (Yannis Monbru Carcelero)

## References

*[J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli
spaces of pseudo-holomorphic curves*, Section A.1][Pardon2016]
*[Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]

-/

@[expose] public section

universe z w v u

open Topology CategoryTheory TopologicalSpace Compacts Opposite Limits

/-A envoyer dans  Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-/

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (hL : ∀ X, Q (L.obj (P.ι.obj X))) (hR : ∀ Y, P (R.obj (Q.ι.obj Y)))

noncomputable def Adjunction.restrictFullSubcategory : Q.lift (P.ι ⋙ L) hL ⊣ P.lift (Q.ι ⋙ R) hR :=
  Adjunction.restrictFullyFaithful adj P.fullyFaithfulι Q.fullyFaithfulι (eqToIso rfl) (eqToIso rfl)

@[simp]
lemma Adjunction.restrictFullSubcategory_unit_app (X : P.FullSubcategory) :
    ((Adjunction.restrictFullSubcategory adj hL hR).unit.app X).hom = adj.unit.app (P.ι.obj X) := by
  simpa using (show ((Adjunction.restrictFullSubcategory adj hL hR).unit.app X).hom = _ from
    Adjunction.map_restrictFullyFaithful_unit_app adj P.fullyFaithfulι Q.fullyFaithfulι
    (eqToIso rfl) (eqToIso rfl) X)

@[simp]
lemma Adjunction.restrictFullSubcategory_counit_app (Y : Q.FullSubcategory) :
  ((Adjunction.restrictFullSubcategory adj hL hR).counit.app Y).hom = adj.counit.app (Q.ι.obj Y) :=
    by
  simpa using (show ((Adjunction.restrictFullSubcategory adj hL hR).counit.app Y).hom = _ from
    Adjunction.map_restrictFullyFaithful_counit_app adj P.fullyFaithfulι Q.fullyFaithfulι
    (eqToIso rfl) (eqToIso rfl) Y)

def Lres := Q.lift (P.ι ⋙ L) hL

def Rres := P.lift (Q.ι ⋙ R) hR


noncomputable def adjRes : Lres hL ⊣ Rres hR := by
  apply Adjunction.restrictFullyFaithful adj P.fullyFaithfulι Q.fullyFaithfulι (eqToIso rfl) (eqToIso rfl)

lemma adjunit (X : P.FullSubcategory) :
    ((adjRes adj hL hR).unit.app X).hom = adj.unit.app (P.ι.obj X) := by
  --simp [adjRes]
  let h : ((adjRes adj hL hR).unit.app X).hom = _ :=
    Adjunction.map_restrictFullyFaithful_unit_app (L := Lres hL) (R := Rres hR) adj
    P.fullyFaithfulι Q.fullyFaithfulι (eqToIso rfl) (eqToIso rfl) X



  rw [h]
  simp
  unfold Lres Rres

  simp




/-fin-/

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

namespace KPresheaf

variable [T2Space X]

/-- For`K`a compact and `P`a K-presheaf verifying the third axiom of K-sheaves, this is
a recipe to build maps from `P.obj (op K)` by only using the open relatively
compact neighbourhoods and not all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {G : (K.openRcNhds)ᵒᵖ ⥤ A} (t : Cocone G)
    (α : (K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P) ⟶ G) :
    P.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).symm h ).map t α

@[ext]
lemma hom_ext_of_isColimit_coconeOfCompacts (P : KPresheaf A X) {K : Compacts X}
    (h : (IsColimit (P.coconeOfCompacts K)))
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

variable (X A) in
/-- The object property of being a K-sheaf -/
abbrev KPresheaf.isKSheaf : ObjectProperty (KPresheaf A X) := fun P ↦ P.IsKSheaf

variable (X A) in
/-- The category of K-sheaves taking values in `A` on a T2Space. -/
abbrev KSheaf := ObjectProperty.FullSubcategory (KPresheaf.isKSheaf A X)

namespace KSheaf

/-- If `P` is a K-sheaf, its the evidence that for any `K`a compact subset of `X`,
 `P.obj.coconeOfCompacts K` is a colimit cocone
-/
@[no_expose]
noncomputable def isColimit (P : KSheaf A X) (K : Compacts X) :
    IsColimit (P.obj.coconeOfCompacts K) :=
  (P.property.nonempty_isColimit_coconeOfCompacts K).some

lemma isoOfIsIsoApp {F G : KSheaf A X} (τ : F ⟶ G)
    (h : ∀ (K : Compacts X), IsIso <| τ.hom.app (op K)) : IsIso τ :=
  (ObjectProperty.isIso_hom_iff τ).mp
  <| (NatTrans.isIso_iff_isIso_app τ.hom).2 (fun Ko => h Ko.unop)

/-- For`K`a compact and `P`a KSheaf, this is a recipi to build maps from
`P.obj (op K)` by only using the open relatively comapct neighbourhoods and not
all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KSheaf A X) (K : Compacts X) {G : (K.openRcNhds)ᵒᵖ ⥤ A}
    (t : Cocone G)
    (α : (K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Set.mono_coe _).functor.op ⋙ P.obj) ⟶ G) :
    P.obj.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).symm (P.isColimit K)).map t α

@[ext]
lemma hom_ext_of_compacts (P : KSheaf A X) {K : Compacts X} {W : A} {f f' : P.obj.obj (op K) ⟶ W}
    (w : ∀ V, dsimp% (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f =
    (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f') : f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv K.openRcNhdsToCompactNhds_mono.functor.op _).symm
    (P.isColimit K)).hom_ext w

end KSheaf

/- A partir de la c'est moins propre normalement-/

noncomputable section


namespace Sheaf

open Presheaf

variable [HasColimitsOfSize.{w, w, v, u} A]

lemma toKPresheafFunctorObjIsKSheaf (F : Presheaf A X) (hF : Presheaf.IsSheaf F) :
    (F.toKPresheafFunctorObj).IsKSheaf := by
  sorry

lemma toKPresheafFunctorObjIsKSheaf' (F : Sheaf A X) :
    (((forget A X).obj F).toKPresheafFunctorObj).IsKSheaf :=
  toKPresheafFunctorObjIsKSheaf _ F.property

@[implicit_reducible]
def toKSheafFunctor : Sheaf A X ⥤ KSheaf A X :=
  ObjectProperty.lift _ (Sheaf.forget A X ⋙ toKPresheafFunctor ) toKPresheafFunctorObjIsKSheaf'

variable (F : Sheaf A X)


@[simp]
lemma truc1 : (toKSheafFunctor.obj F).obj = ((forget A X).obj F).toKPresheafFunctorObj := by rfl

variable {F} in
@[ext]
lemma toKSheafFunctorObjObj_hom_ext {Y : A} {K : (Compacts X)ᵒᵖ}
    (f g : (toKSheafFunctor.obj F).obj.obj K ⟶ Y)
    (h : ∀ U : K.unop.openNhds, ((forget A X).obj F).ιToKPresheafFunctorObjObj U ≫ f =
      ((forget A X).obj F).ιToKPresheafFunctorObjObj U ≫ g) :
    f = g := toKPresheafFunctorObjObj_hom_ext _ _ h

@[simp]
lemma truc [HasLimitsOfSize.{w, w, v, u} A] {U : Opens X} (K : U.compactsInside) :
    (toKSheafFunctor.obj F).obj.πToPresheafFunctorObjObj K =
   (toKPresheafFunctorObj F.obj).πToPresheafFunctorObjObj K := by
  rfl


end Sheaf

namespace KSheaf

open KPresheaf

variable [HasLimitsOfSize.{w, w, v, u} A]

lemma toPresheafFunctorObjIsSheaf (F : KPresheaf A X) (hF : KPresheaf.IsKSheaf F) :
    (F.toPresheafFunctorObj).IsSheaf := by
  sorry

lemma toPresheafFunctorObjIsSheaf' (F : KSheaf A X) :
    (F.obj.toPresheafFunctorObj).IsSheaf := by
  sorry

@[implicit_reducible]
def toSheafFunctor : KSheaf A X ⥤ Sheaf A X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ toPresheafFunctor) (toPresheafFunctorObjIsSheaf')

variable (G : KSheaf A X)

variable {G} in
@[ext]
lemma toKSheafFunctorObjObj_hom_ext {U : (Opens X)ᵒᵖ} {Y : A}
    (f g : Y ⟶ (toSheafFunctor.obj G).obj.obj U)
    (h : ∀ K : U.unop.compactsInside, f ≫ G.obj.πToPresheafFunctorObjObj K =
      g ≫  G.obj.πToPresheafFunctorObjObj K) : f = g :=
  toPresheafFunctorObjObj_hom_ext _ _ h

open Sheaf

variable [HasColimitsOfSize.{w, w, v, u} A]

/-- The adjunction between `toKSheafFunctor` and `toSheafFunctor` obtained by restricting the one
between `toKPresheafFunctor` and `toPresheafFunctor`
-/
@[simps!]
 def adjunction : (toKSheafFunctor (A := A) (X := X)) ⊣ (toSheafFunctor ) :=
  --Adjunction.restrictFullSubcategory (KPresheaf.adjunction) _ _
  --ça je le laisse pour raconter l'histoire TODO: à enlever
  Adjunction.restrictFullyFaithful (KPresheaf.adjunction)
  (Functor.FullyFaithful.ofFullyFaithful (Sheaf.forget A X))
  ((isKSheaf A X).fullyFaithfulι) (Iso.refl _ ) (Iso.refl _)

--set_option backward.isDefEq.respectTransparency false
@[simp]
lemma adjunction.unit_app (F : Sheaf A X) :
    (adjunction.unit.app F).hom = (KPresheaf.adjunction.unit.app F.obj) := Adjunction.restrictFullSubcategory_unit_app _ _ _ _


  /-simpa using (show (adjunction.unit.app F).hom = _ from Adjunction.map_restrictFullyFaithful_unit_app
    (KPresheaf.adjunction (A := A) (X := X)) (Functor.FullyFaithful.ofFullyFaithful
    (Sheaf.forget A X)) ((isKSheaf A X).fullyFaithfulι) _ _ F)


  rw [this]
  simp
  rfl
  unfold toKSheafFunctor toSheafFunctor
  simp
  rfl -- ça ça marche avec des defeqabuses-/
@[simp]
lemma adjunction.counit_app (G : KSheaf A X) :
    (adjunction.counit.app G).hom = (KPresheaf.adjunction.counit.app G.obj) :=
  Adjunction.restrictFullSubcategory_counit_app _ _ _ _

--set_option backward.defeqAttrib.useBackward true in
--set_option backward.isDefEq.respectTransparency false in
lemma truc (F : Presheaf A X) (hF : F.IsSheaf) :  IsIso ((KPresheaf.adjunction.unit.app F)) := by
  suffices ∀ U, IsIso ((adjunctionUnit'.app F).app U) by
    simpa using NatIso.isIso_of_isIso_app _
  intro U
  constructor
  let inv : ((Presheaf.toKPresheafFunctor ⋙ toPresheafFunctor).obj F).obj U ⟶ ((𝟭 (Presheaf A X)).obj F).obj U := by
    dsimp
    have : F.IsSheafOpensLeCover := by
      apply (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).1 hF



    let V : U.unop.compactsInside → (Opens X) := fun K => ⟨interior K, isOpen_interior⟩

    let s : Cone ((ObjectProperty.ι fun V_1 ↦ ∃ i, V_1 ≤ V i).op ⋙ F) :=
      ⟨F.toKPresheafFunctorObj.toPresheafFunctorObjObj (unop U),
      ⟨fun W => by
        let cW : Compacts X := ⟨closure W.unop.obj,by
            obtain ⟨⟨K,_⟩,hK⟩ := W.unop.property
            exact IsCompact.closure_of_subset K.isCompact <| Set.Subset.trans hK interior_subset⟩
        refine F.toKPresheafFunctorObj.πToPresheafFunctorObjObj ?_ ≫ ?_

        · exact ⟨cW,by
            obtain ⟨⟨K,hKU⟩,hK⟩ := W.unop.property
            exact Set.Subset.trans (closure_minimal (Set.Subset.trans hK interior_subset)
              <| IsCompact.isClosed K.isCompact) hKU⟩

        · let s : Cocone ((Set.mono_coe cW.openNhds).functor.op ⋙ F) := ⟨F.obj (op (unop W).obj),sorry⟩
          exact (F.isColimitToKPresheafFunctorObjObjCocone cW ).desc s,sorry⟩⟩

    apply (this V).some.lift s ≫ F.map (op (eqToHom ?_))

    dsimp [V]
    sorry
  use inv
  constructor
  · unfold inv
    aesop
    sorry

  · sorry

instance (F : Sheaf A X) : IsIso (adjunction.unit.app F) := by
  apply (ObjectProperty.isIso_hom_iff _).1
  simp only [adjunction.unit_app]
  apply truc _ F.property

instance (F : KSheaf A X) : IsIso (adjunction.counit.app F) := by

  apply isoOfIsIsoApp
  intro K
  simp [adjunction, ]
  --simp
  sorry




/-- The isomorphism between the category of sheaves and the category of Ksheaves

Hyp will be added but the goal is to keep the two newt examples compiling.
-/
def KshIsoSh : (Sheaf A X) ≌ (KSheaf A X) :=
  Adjunction.toEquivalence (KSheaf.adjunction)

example : (Sheaf (Type w) X) ≌ (KSheaf (Type w) X) := KshIsoSh

example : (Sheaf Ab X) ≌ (KSheaf Ab X) := KshIsoSh

end KSheaf

end

end TopCat
/-
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in-/
