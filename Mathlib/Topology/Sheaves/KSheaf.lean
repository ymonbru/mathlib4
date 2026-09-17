/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/
module

public import Mathlib.Topology.Sheaves.KPresheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Ksheaves

We define K-sheaves on a T2 topological space with value in an arbitrary category.

One may expect this notion to come from sheaves on a site of compact subset of a topological space
but there is no coresponding Grothendieck topology on compact subsets, in particular
because the `nonempty_isColimit_coconeOfCompacts` condition can't be expressed as a
limit condition.
-/

@[expose] public section

universe w v u

open Topology CategoryTheory TopologicalSpace Compacts Opposite Limits

variable {A : Type u} [Category.{v} A] {X : TopCat.{w}}

namespace TopCat

namespace KPresheaf

@[simp]
theorem id_app (P : KPresheaf A X) (K : (Compacts X)ᵒᵖ) : NatTrans.app (𝟙 P) K = 𝟙 _ := rfl

@[simp]
theorem comp_app (P Q R : KPresheaf A X) (K : (Compacts X)ᵒᵖ) (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app K = f.app K ≫ g.app K := rfl

@[ext]
lemma ext (P Q : KPresheaf A X) (f g : P ⟶ Q) (w : ∀ K : Compacts X, f.app (op K) = g.app (op K)) :
    f = g := by
  apply NatTrans.ext
  ext K
  induction K with | _ K => ?_
  apply w

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If `P` is a KPresheaf, and `K` a compact subset then `P.obj (op K)` is equiped with a
structure of cocone over the diagramm defined by the `P.obj (op L)` for `L` a compact
neighbourhood of `K` -/
@[simps]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Subtype.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map <| opHomOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)
  ι.naturality _ _ _ := by
    dsimp
    rw [← P.map_comp, Category.comp_id]
    rfl

/-- For `P` a KPresheaf, and `K` a compact subset then `P.obj (op K)` is equiped with a
structure of cocone over the diagramm defined by the `P.obj (op (closure (U : Set X))`
for `U` an open
neighbourhood of `K` -/
def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X) :=
  Cocone.whisker K.openRcNhdsToCompactNhds_mono.functor.op <| P.coconeOfCompacts K

variable [T2Space X]

set_option backward.isDefEq.respectTransparency false in
/-- For`K`a compact and `P`a KPresheaf verifying the third axiom of KSheaves, this is
a recipi to build maps from `P.obj(op K)` by only using the open relatively
comapct neighbourhoods and not all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KPresheaf A X) (K : Compacts X)
    (h : (IsColimit (P.coconeOfCompacts K))) {G : (K.openRcNhds)ᵒᵖ ⥤ A} (t : Cocone G)
    (α : (K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Subtype.mono_coe _).functor.op ⋙ P) ⟶ G) :
    P.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).map t α

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_K_ext (P : KPresheaf A X) {K : Compacts X} (h : (IsColimit (P.coconeOfCompacts K)))
    {W : A} {f f' : P.obj (op K) ⟶ W}
    (w : ∀ V, (P.coconeOfClosureOfOpens K).ι.app V ≫ f = (P.coconeOfClosureOfOpens K).ι.app V ≫ f')
    : f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).hom_ext w

set_option backward.isDefEq.respectTransparency false in
/-- The Ksheaf condition. It's a generalisation of the one of J.Pardon that
corespond to the one of J.Lurie in the case of usual categories.

There is no coresponding Grothendieck topology on compact subsets, in particular
because the nonempty_isColimit_coconeOfCompacts condition can't be expressed as a
limit condition. -/
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
/-- The category of Ksheaves taking values in `A` on a T2Space. -/
abbrev KSheaf := ObjectProperty.FullSubcategory (KPresheaf.isKSheaf A X)

namespace KSheaf

variable [T2Space X]

lemma isoOfIsIsoApp {F G : KSheaf A X} (τ : F ⟶ G)
    (h : ∀ (K : Compacts X), IsIso <| τ.hom.app (op K)) : IsIso τ :=
  (ObjectProperty.isIso_hom_iff τ).mp
  <| (NatTrans.isIso_iff_isIso_app τ.hom).2 (fun Ko => h Ko.unop)

set_option backward.isDefEq.respectTransparency false in
/-- For`K`a compact and `P`a KSheaf, this is a recipi to build maps from
`P.obj (op K)` by only using the open relatively comapct neighbourhoods and not
all the compacts neighbourhoods. -/
noncomputable def mapOfOpenClosure (P : KSheaf A X) (K : Compacts X) {G : (K.openRcNhds)ᵒᵖ ⥤ A}
    (t : Cocone G)
    (α : (K.openRcNhdsToCompactNhds_mono.functor.op ⋙ (Subtype.mono_coe _).functor.op ⋙ P.obj) ⟶ G)
    : P.obj.obj (op K) ⟶ t.pt :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun
  (Classical.choice <| P.property.nonempty_isColimit_coconeOfCompacts K) ).map t α

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_K_ext (P : KSheaf A X) {K : Compacts X} {W : A} {f f' : P.obj.obj (op K) ⟶ W}
    (w : ∀ V, (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f =
    (P.obj.coconeOfClosureOfOpens K).ι.app V ≫ f') : f = f' :=
  ((Functor.Final.isColimitWhiskerEquiv _ _).invFun
  (Classical.choice <| P.property.nonempty_isColimit_coconeOfCompacts K)).hom_ext w

end KSheaf

/- A partir de la c'est moins propre normalement-/

noncomputable section

variable [T2Space X]

namespace Sheaf

open Presheaf

variable [HasColimitsOfSize.{w, w, v, u} A]

lemma toKPresheafFunctorObjIsKSheaf (F : Presheaf A X) (hF : Presheaf.IsSheaf F) :
    (F.toKPresheafFunctorObj).IsKSheaf := by
  sorry

lemma toKPresheafFunctorObjIsKSheaf' (F : Sheaf A X) :
    (((forget A X).obj F).toKPresheafFunctorObj).IsKSheaf :=
  toKPresheafFunctorObjIsKSheaf _ F.property

def toKSheafFunctor : Sheaf A X ⥤ KSheaf A X :=
  ObjectProperty.lift _ (Sheaf.forget A X ⋙ toKPresheafFunctor ) toKPresheafFunctorObjIsKSheaf'

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


def toSheafFunctor : KSheaf A X ⥤ Sheaf A X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ toPresheafFunctor) (toPresheafFunctorObjIsSheaf')



open Sheaf

variable [HasColimitsOfSize.{w, w, v, u} A]

/-- The adjunction between `toKSheafFunctor` and `toSheafFunctor` obtained by restricting the one
between `toKPresheafFunctor` and `toPresheafFunctor`
-/
 def adjunction : (toKSheafFunctor (A := A) (X := X)) ⊣ (toSheafFunctor ) :=
  Adjunction.restrictFullyFaithful (KPresheaf.adjunction)
  (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
  (Iso.refl _) (Iso.refl _)

variable (F : Sheaf A X)

#check adjunction.unit.app F

lemma truc (F : Presheaf A X) (hF : F.IsSheaf) :  IsIso ((KPresheaf.adjunction.unit.app F)) := by
  #check  isoOfIsIsoApp (KPresheaf.adjunction.unit.app F)

  sorry


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (F : Sheaf A X) : IsIso (adjunction.unit.app F) := by
 #check isoOfIsIsoApp (adjunction.unit.app F)

  #check Adjunction.instIsIsoAppUnitOfFullOfFaithful

  have : ∀ x, IsIso ((adjunction.unit.app F).app x) := by sorry
  rw [NatTrans.isIso_iff_isIso_app]
  constructor
  apply?
  sorry

instance (F : KSheaf A X) : IsIso (adjunction.counit.app F) := by

  apply isoOfIsIsoApp
  intro K
  simp [adjunction, ]
  simp
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

#min_imports
