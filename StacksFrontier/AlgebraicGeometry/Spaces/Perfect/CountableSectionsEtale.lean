module

public import StacksFrontier.Algebra.Category.Grp.CountableCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Countable cohomology over the quasi-compact quasi-separated étale objects of a space

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S`, and suppose we are
given, for every presheaf `Y` with a map to `X`, an object `RΓ Y` of the derived category of
abelian groups — think of it as `RΓ(Y, K ⊗^𝐋 E)` for a fixed pair of coefficients. This file
shows that countability of the cohomology of `RΓ` **spreads from the affine étale objects to all
of the quasi-compact quasi-separated ones**, provided `RΓ` turns each elementary distinguished
square into a Mayer–Vietoris distinguished triangle.

That is the devissage half of Stacks 0CRU, and it is proved here unconditionally:

* `hasCountableCohomology_of_edsSectionsTriangle` turns one Mayer–Vietoris triangle into the
  countability statement at its first vertex. The countable abelian groups are a Serre class, so
  this is the two-out-of-three principle of `AddCommGrpCat.HasCountableCohomology.obj₁` applied
  to the biproduct `RΓ(U) ⊞ RΓ(V)`.
* `hasCountableCohomology_of_qcqs_etale` feeds that step to the induction principle of
  Stacks 08GP, `AlgebraicGeometry.Space.qcqs_induction_on`.

## Why the coefficients are abstracted into `RΓ`

The predicate argument of `qcqs_induction_on` has type
`(Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.obj) → Prop`: it ranges over a **raw presheaf**
together with a map to `X`, not over an object of the spaces-étale site. It has to, because the
induction visits the open subfunctor `U.toFunctor` of a site object and the fibre product
`pullback U.ι f`, and neither of those is packaged as a site object. Cohomology, by contrast, is
defined on site objects. So any use of this induction principle for a cohomological property
must first choose an extension of that property to arbitrary presheaves over `X`, and `RΓ` is
exactly that choice, made a parameter here instead of being fixed. The triangle hypothesis
`hMV` is stated in the shape `Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ` that
Stacks 0CRS produces, so the two compose directly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AddCommGrpCat (HasCountableCohomology)

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasDerivedCategory.{w} AddCommGrpCat.{u}]

/-- **The Mayer–Vietoris step for countability.** Given the Mayer–Vietoris distinguished triangle
`RΓ(W) ⟶ RΓ(U) ⊞ RΓ(V) ⟶ RΓ(U ×_W V) ⟶ RΓ(W)⟦1⟧` of an elementary distinguished square, if the
cohomology of `RΓ(U)`, `RΓ(V)` and `RΓ(U ×_W V)` is countable in every degree then so is that of
`RΓ(W)`.

The countable abelian groups form a Serre class, so countability is a two-out-of-three property
along a distinguished triangle; the middle vertex is a biproduct, which is handled by
`AddCommGrpCat.HasCountableCohomology.biprod`. -/
theorem hasCountableCohomology_of_edsSectionsTriangle
    {RW RU RV RP : DerivedCategory AddCommGrpCat.{u}}
    {fU : RW ⟶ RU} {fV : RW ⟶ RV} {gU : RU ⟶ RP} {gV : RV ⟶ RP}
    {δ : RP ⟶ RW⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
      distTriang (DerivedCategory AddCommGrpCat.{u}))
    (hU : HasCountableCohomology RU) (hV : HasCountableCohomology RV)
    (hP : HasCountableCohomology RP) :
    HasCountableCohomology RW :=
  HasCountableCohomology.obj₁ _ hT (hU.biprod hV) hP

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The devissage of Stacks 0CRU.** Let `X` be a quasi-compact quasi-separated algebraic space
over `S` and let `RΓ` assign to every presheaf over `X` an object of the derived category of
abelian groups. If

* the cohomology of `RΓ` is countable over every *affine* object of the spaces-étale site of `X`,
  and
* every elementary distinguished square `(U ⊆ W, V ⟶ W)` gives rise to a Mayer–Vietoris
  distinguished triangle `RΓ(W) ⟶ RΓ(U) ⊞ RΓ(V) ⟶ RΓ(U ×_W V) ⟶ RΓ(W)⟦1⟧`,

then the cohomology of `RΓ` is countable over *every* quasi-compact quasi-separated object of the
spaces-étale site of `X`.

This is the second and third paragraphs of the proof of Stacks 0CRU: the induction principle of
Stacks 08GP reduces the lemma to the affine case together with the Mayer–Vietoris step, and the
latter is `hasCountableCohomology_of_edsSectionsTriangle`. -/
theorem hasCountableCohomology_of_qcqs_etale
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (RΓ : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.obj) →
      DerivedCategory AddCommGrpCat.{u})
    (haff : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.obj.left.obj →
      HasCountableCohomology (RΓ V.obj.left.obj V.obj.hom.hom))
    (hMV : ∀ (W V : SpacesEtale B S hS X) (U : Subfunctor W.obj.left.obj)
      (f : V.obj.left.obj ⟶ W.obj.left.obj), f ≫ W.obj.hom.hom = V.obj.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.obj.left.property U f →
      ∃ (fU : RΓ W.obj.left.obj W.obj.hom.hom ⟶ RΓ U.toFunctor (U.ι ≫ W.obj.hom.hom))
        (fV : RΓ W.obj.left.obj W.obj.hom.hom ⟶ RΓ V.obj.left.obj V.obj.hom.hom)
        (gU : RΓ U.toFunctor (U.ι ≫ W.obj.hom.hom) ⟶
          RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom))
        (gV : RΓ V.obj.left.obj V.obj.hom.hom ⟶
          RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom))
        (δ : RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom) ⟶
          (RΓ W.obj.left.obj W.obj.hom.hom)⟦(1 : ℤ)⟧),
        Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
          distTriang (DerivedCategory AddCommGrpCat.{u})) :
    ∀ Y : SpacesEtale B S hS X, IsQuasiCompactSpace B S hS Y.obj.left.obj →
      IsAbsolutelyQuasiSeparated B S hS hZ Y.obj.left.obj →
      HasCountableCohomology (RΓ Y.obj.left.obj Y.obj.hom.hom) := by
  refine qcqs_induction_on B S hS hZ X
    (fun Y g => HasCountableCohomology (RΓ Y g)) haff ?_
  intro W V U f hcomm hsq _ _ _ _ hU hV hP
  obtain ⟨fU, fV, gU, gV, δ, hT⟩ := hMV W V U f hcomm hsq
  exact hasCountableCohomology_of_edsSectionsTriangle hT hU hV hP

section Clauses

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B) (S) (hS) (X : AlgebraicSpaces B S hS)
  [∀ V : (smallEtaleRingedSite B S hS X.obj X.property).C,
    HasSheafify ((smallEtaleRingedSite B S hS X.obj X.property).J.over V) AddCommGrpCat.{u}]

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Stacks 0CRU, the clause on `Ext^i(E|_U, K|_U)`.** Let `X` be a quasi-compact
quasi-separated algebraic space over `S`, let `K` be an object of `D_QCoh(𝒪_X)` and let `E` be a
perfect object of `D(𝒪_X)`. Then for every quasi-compact quasi-separated étale `U ⟶ X` the set
`Ext^i(E|_U, K|_U)` is countable.

The three hypotheses are the three inputs the source proof takes from elsewhere, and they are the
three this library does not supply:

* `hExt` identifies `Ext^i(E|_Y, K|_Y)` with the `i`-th cohomology of a derived-sections object
  `RΓ Y`. This is the content of Stacks 08JJ that the library lacks: the carrier of 08JJ in this
  repository, `Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_localSummand`, proves only the
  undergived sheaf isomorphism `F ⊗ E^∨ ≅ SheafHom(E, F)`, not the derived identity
  `K ⊗^𝐋 E^∨ ≅ RSheafHom(E, K)` that turns `Ext` into cohomology.
* `haff` is the affine case, i.e. Stacks 0CRP transported to the spaces-étale site. The 0CRP
  carrier in this repository is about quasi-compact opens of a *scheme* and assumes its own
  affine case, so it does not supply this.
* `hMV` is the Mayer–Vietoris triangle of an elementary distinguished square, i.e. Stacks 0CRS.
  The 0CRS carrier here is conditional on part (1) of Stacks 08GW, which is itself unproved.

Granted those, the devissage is `hasCountableCohomology_of_qcqs_etale`.

Perfectness of `E` is part of the statement of Stacks 0CRU and is kept here, but it is not
consumed by this proof: in the source argument perfectness is used exactly inside the affine case
and inside the reduction of `Ext` to cohomology, and both of those are the hypotheses `haff` and
`hExt`. The binder is therefore written `_hE`. -/
@[stacks 0CRU "the sets Ext^i(E|_U, K|_U)"]
theorem countable_ext_of_qcqs_etale (hZ : B.Contains (⊤_ Scheme.{u}))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.obj X.property)
    (E : DerivedCategory (Modules.{u, u} B S hS X.obj X.property))
    (_hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.obj X.property) E)
    (RΓ : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.obj) →
      DerivedCategory AddCommGrpCat.{u})
    (hExt : ∀ (Y : SpacesEtale B S hS X) (hY : IsEtale B S hS Y.obj.hom.hom) (j : ℤ),
      Nonempty (DerivedCategory.Ext
        ((etaleModulePullback.{u, u} B S hS (Y := X) ⟨Y.obj.hom.hom⟩ hY).mapDerivedCategory.obj E)
        ((etaleModulePullback.{u, u} B S hS (Y := X) ⟨Y.obj.hom.hom⟩ hY).mapDerivedCategory.obj
          K.obj) j ≃
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
          (RΓ Y.obj.left.obj Y.obj.hom.hom)))
    (haff : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.obj.left.obj →
      HasCountableCohomology (RΓ V.obj.left.obj V.obj.hom.hom))
    (hMV : ∀ (W V : SpacesEtale B S hS X) (U : Subfunctor W.obj.left.obj)
      (f : V.obj.left.obj ⟶ W.obj.left.obj), f ≫ W.obj.hom.hom = V.obj.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.obj.left.property U f →
      ∃ (fU : RΓ W.obj.left.obj W.obj.hom.hom ⟶ RΓ U.toFunctor (U.ι ≫ W.obj.hom.hom))
        (fV : RΓ W.obj.left.obj W.obj.hom.hom ⟶ RΓ V.obj.left.obj V.obj.hom.hom)
        (gU : RΓ U.toFunctor (U.ι ≫ W.obj.hom.hom) ⟶
          RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom))
        (gV : RΓ V.obj.left.obj V.obj.hom.hom ⟶
          RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom))
        (δ : RΓ (pullback U.ι f) (pullback.fst U.ι f ≫ U.ι ≫ W.obj.hom.hom) ⟶
          (RΓ W.obj.left.obj W.obj.hom.hom)⟦(1 : ℤ)⟧),
        Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
          distTriang (DerivedCategory AddCommGrpCat.{u}))
    (U : SpacesEtale B S hS X) (hU : IsEtale B S hS U.obj.hom.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.obj.left.obj) (i : ℤ) :
    Countable (DerivedCategory.Ext
      ((etaleModulePullback.{u, u} B S hS (Y := X) ⟨U.obj.hom.hom⟩ hU).mapDerivedCategory.obj E)
      ((etaleModulePullback.{u, u} B S hS (Y := X) ⟨U.obj.hom.hom⟩ hU).mapDerivedCategory.obj K.obj)
      i) := by
  have hcount := hasCountableCohomology_of_qcqs_etale hZ X RΓ haff hMV U hUqc hUqs i
  obtain ⟨e⟩ := hExt U hU i
  have := hcount
  exact e.injective.countable

end Clauses

end AlgebraicGeometry.Space

end
