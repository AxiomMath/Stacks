module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiQuasicoherentDescent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.KFlat.ChosenResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorProductCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of complexes with quasi-coherent cohomology

Let `X` be a scheme and let `D_QCoh(𝒪_X) ⊆ D(𝒪_X)` be the full subcategory of the unbounded
derived category of `𝒪_X`-modules consisting of the complexes all of whose cohomology sheaves
are quasi-coherent. [Stacks, Tag 08DX] part (1) asserts that this subcategory is closed under the
derived tensor product: if every cohomology sheaf of `K` and of `L` is quasi-coherent, then so is
every cohomology sheaf of `K ⊗ᴸ_{𝒪_X} L`.

The proof is the one of the source. Quasi-coherence of a sheaf of modules is local on `X`, so it
suffices to prove the assertion after restriction to each member of the affine open cover
`AlgebraicGeometry.Scheme.affineOpenCover`, whose members are spectra of rings. On `Spec R` the
restrictions of `K` and `L` are derived sheafifications of complexes of `R`-modules — that is
[Stacks, Tag 06Z0], available here as the equivalence
`AlgebraicGeometry.derivedTilde_isEquivalence` — and part (2) of the tag identifies the derived
tensor product of two derived sheafifications with the derived sheafification of a complex of
`R`-modules, whose cohomology sheaves are quasi-coherent by
`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj`. Only the existence of such a
complex is used, and it is extracted from the complex-level half of part (2), the totalised
affine tensor comparison `AlgebraicGeometry.affineTensorComplexIso`.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_derivedTensor` — [Stacks, Tag 08DX] part (1): for
  `K, L` in `D_QCoh(𝒪_X)` every cohomology sheaf of `K ⊗ᴸ_{𝒪_X} L` is quasi-coherent.
* `Stacks.Duality.quasiCoherentDerivedTensor` — the same statement as structure: the derived
  tensor product restricts to a bifunctor
  `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X)`.

## Main definitions

* `Stacks.Duality.derivedTensor` — `⊗ᴸ_{𝒪_X}` on `D(𝒪_X)` for a scheme `X`, namely the derived
  tensor product of [Stacks, Tag 06YH] read on the ringed space underlying `X`.
* `Stacks.Duality.derivedTensorIsoQTensorComplex` — on K-flat representatives the derived tensor
  product is the total tensor complex.
* `Stacks.Duality.derivedTensorDerivedTildeIsoOfKFlat` — for K-flat complexes `P, P'` of
  `R`-modules, `P̃ ⊗ᴸ_{𝒪_{Spec R}} P̃' ≅ (Tot(P ⊗_R P'))~`.
* `Stacks.Duality.pullbackHomologyDerivedTensorIso` — the whole of the local computation, for an
  open immersion `g : Spec R ⟶ X`: `g^*H^i(Q(Tot(P ⊗ Q))) ≅ H^i(Q(g^*P) ⊗ᴸ Q(g^*Q))`.

## Implementation notes

*The restriction to an open is made at the level of complexes, not of derived categories.* The
source reduces to the affine case using [Stacks, Tag 079U], the bifunctorial isomorphism
`Lg^*(K ⊗ᴸ L) ≅ Lg^*K ⊗ᴸ Lg^*L`, of which the repository has the value on K-flat
representatives only, and at a derived-category model of its own choosing. None of that is
needed. For an open immersion `g` the functor `g^*` is exact, so `g^*` commutes with the
cohomology of the derived category by `AlgebraicGeometry.derivedHomologyMapIso`, and the
remaining input is the *complex-level* identity
`g^*Tot(P ⊗_{𝒪_X} Q) ≅ Tot(g^*P ⊗_{𝒪_{Spec R}} g^*Q)` of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso`, which mentions no
derived category at all. The derived tensor product then enters only through the `comparison`
field of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, once on `X` and once on
`Spec R`.

*The model of the derived categories.* Everything is at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is what instance search finds with
no local attribute in scope, and no declaration here mentions
`CategoryTheory.HasDerivedCategory.standard`. This is forced rather than chosen: [Stacks,
Tag 06Z0] is formalized as `AlgebraicGeometry.derivedTilde_isEquivalence`, whose file carries no
`HasDerivedCategory` binder, so essential surjectivity of derived sheafification is available at
the locally small model and at no other. The derived tensor product of [Stacks, Tag 06YH] is
available there too: it is stated over `StrictlyPerfect.OXMod X.toRingedSpace`, which is a
reducible abbreviation for a category of sheaves of modules, so the global instance
`SheafOfModules.hasDerivedCategory` supplies its model and
`DerivedCategory (StrictlyPerfect.OXMod X.toRingedSpace)` is `DerivedCategory X.Modules` by `rfl`.

*Two spellings of the category of `𝒪_X`-modules.* `X.Modules` is an opaque `def` whose `Category`
instance is built from, but not syntactically equal to, the one on
`SheafOfModules X.ringCatSheaf`; and the tensor product of sheaves of modules is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, a third spelling of the same sheaf of rings.
The three are `rfl`-equal and the conversion check crosses them in term position, but instance
search does not. Complexes are therefore declared at the tensor spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, which is the spelling the K-flatness
predicate and the total tensor complex are stated at, and the crossing to `X.Modules` is made by
a type ascription on `DerivedCategory.Q.obj P` wherever a derived category of `X` is meant. The
ascription is load-bearing: without it the universe of the derived category of the tensor
spelling is an unsolved metavariable when the `Category` instance of the ambient `Iso` is
synthesized.

*The cover.* The affine *open cover* `AlgebraicGeometry.Scheme.affineOpenCover` is used rather
than the family of affine opens of `X`, because its members are by construction `Spec` of a ring
— `AffineCover.f j : Spec (𝒰.X j) ⟶ S` — whereas an affine open `U` only satisfies `IsAffine
U.toScheme` and would have to be moved to `Spec Γ(U, ⊤)` along `U.toScheme.isoSpec`, which would
require transporting the derived tensor product along an isomorphism of schemes. The price is the
isomorphism `g.isoOpensRange` between the source of a cover map and its open image, which is paid
once, on sheaves of modules.

*What is taken from part (2), and why it is not the whole of it.* The affine case needs only that
the derived tensor product of two derived sheafifications is *some* derived sheafification, which
is `Stacks.Duality.exists_iso_derivedTilde_derivedTensor`. That existence statement is proved
here from the totalised affine tensor comparison
`AlgebraicGeometry.affineTensorComplexIso` — part (2) at the level of complexes — by exhibiting
the witness `W = Q(Tot(P ⊗_R P'))` for K-flat representatives `P, P'` of the two arguments. It is
strictly weaker than part (2), which identifies the left-hand side with `(M ⊗ᴸ_R N)~`, and it
therefore carries no tag. The reason for taking the weaker form is a model clash on the module
side: the `comparison` field of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` was elaborated with
`CategoryTheory.HasDerivedCategory.standard` in scope, so naming the module-side derived tensor
product would drag the standard model into a statement whose other half — [Stacks, Tag 06Z0] —
exists only at the locally small one. The ordinary total tensor complex has no such problem,
being no derived category's object, and its sheafification is a genuine object of the locally
small `D(R)`.

*Currying.* The restricted bifunctor is assembled by lifting the uncurried derived tensor product
to the full subcategory and currying the result; in this version of Mathlib the two functors
involved are `CategoryTheory.Functor.uncurry` and `CategoryTheory.Functor.curryObj`.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w u

namespace Stacks.Duality

/-! ### The derived tensor product on a scheme -/

/-- **`⊗ᴸ_{𝒪_X}`, the derived tensor product on `D(𝒪_X)` for a scheme `X`.** A scheme is a ringed
space and a ringed space is the ringed site of its opens, so this is the derived tensor product
of [Stacks, Tag 06YH], namely `Stacks.Cohomology.TorAmplitude.derTensor`, with its two derived
categories spelled in the scheme form. -/
abbrev derivedTensor (X : Scheme.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor

/-- A cochain complex of `𝒪_X`-modules, in the spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` of the category of `𝒪_X`-modules that the
tensor product of sheaves of modules and the K-flatness predicate of [Stacks, Tag 06YN] are
stated at. It is `CochainComplex X.Modules ℤ` by `rfl`. -/
abbrev TensorComplex (X : Scheme.{u}) : Type (u + 1) :=
  CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) ℤ

/-- **K-flatness of a complex of `𝒪_X`-modules** ([Stacks, Tag 06YN]): the total tensor complex
`Tot(G ⊗_{𝒪_X} P)` is acyclic for every acyclic complex `G` of `𝒪_X`-modules. -/
abbrev KFlatComplex {X : Scheme.{u}} (P : TensorComplex X) : Prop :=
  CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) P

/-- `Tot(P ⊗_{𝒪_X} Q)`, the total tensor complex of two complexes of `𝒪_X`-modules
([Stacks, Tag 06YM]). -/
abbrev totalTensorComplex {X : Scheme.{u}} (P Q : TensorComplex X) : TensorComplex X :=
  ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P).obj Q

/-- **Derived sheafification `D(R) ⥤ D(𝒪_{Spec R})`**, before the quasi-coherence of the
cohomology sheaves is recorded: the derived functor of the exact functor `M ↦ M̃`. -/
abbrev derivedTildeFunctor (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (Spec R).Modules :=
  (tilde.functor R).mapDerivedCategory

/-! ### K-flat representatives -/

/-- **Every object of `D(𝒪_X)` is the class of a K-flat complex.** This is [Stacks, Tag 06YS],
the existence of K-flat resolutions, together with the fact that a quasi-isomorphism becomes
invertible in the derived category. -/
theorem exists_kFlatComplex_iso (X : Scheme.{u}) (E : DerivedCategory X.Modules) :
    ∃ P : TensorComplex X, KFlatComplex P ∧
      Nonempty ((DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅ E) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.sheaf
    (DerivedCategory.Q.objPreimage E)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := Stacks.DerivedTensor.RingedSite.Modules X.sheaf) p).2 hp
  exact ⟨P, hP, ⟨@asIso _ _ _ _ (DerivedCategory.Q.map p) hiso ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- **On K-flat representatives the derived tensor product is the total tensor complex.** If `P`
and `Q` are K-flat complexes of `𝒪_X`-modules whose classes in `D(𝒪_X)` are `E` and `F`, then
`E ⊗ᴸ_{𝒪_X} F ≅ Q(Tot(P ⊗_{𝒪_X} Q))`. This is the `comparison` field of the derived tensor
product, transported along the two chosen isomorphisms. -/
def derivedTensorIsoQTensorComplex (X : Scheme.{u}) (E F : DerivedCategory X.Modules)
    (P Q : TensorComplex X) (hP : KFlatComplex P) (hQ : KFlatComplex Q)
    (eP : (DerivedCategory.Q.obj P : DerivedCategory X.Modules) ≅ E)
    (eQ : (DerivedCategory.Q.obj Q : DerivedCategory X.Modules) ≅ F) :
    ((derivedTensor X).obj E).obj F ≅
      (DerivedCategory.Q.obj (totalTensorComplex P Q) : DerivedCategory X.Modules) :=
  (((derivedTensor X).mapIso eP).app F).symm ≪≫
    ((derivedTensor X).obj (DerivedCategory.Q.obj P)).mapIso eQ.symm ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparison P Q hP hQ

/-! ### Locality over the affine open cover -/

/-- **Quasi-coherence is local over the affine open cover** ([Stacks, Tag 01BE]). A sheaf of
`𝒪_X`-modules whose restriction along every open immersion `Spec R ⟶ X` is quasi-coherent is
quasi-coherent.

The members of `AlgebraicGeometry.Scheme.affineOpenCover` are open immersions from spectra of
rings and their images cover `X`, and the restriction to the image of such a map differs from the
restriction along the map itself by the isomorphism
`AlgebraicGeometry.Scheme.Hom.isoOpensRange` onto the open image. -/
theorem isQuasicoherent_of_restrict_spec (X : Scheme.{u}) (M : X.Modules)
    (h : ∀ (R : CommRingCat.{u}) (g : Spec R ⟶ X) [IsOpenImmersion g],
      ((Scheme.Modules.restrictFunctor g).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  refine AlgebraicGeometry.isQuasicoherent_of_restrict_openCover M
    (fun i : X.affineOpenCover.I₀ => (X.affineOpenCover.f i).opensRange)
    X.affineOpenCover.openCover.iSup_opensRange fun i => ?_
  have hg : ((Scheme.Modules.restrictFunctor (X.affineOpenCover.f i)).obj M).IsQuasicoherent :=
    h _ (X.affineOpenCover.f i)
  have hres : (((Scheme.Modules.restrictFunctor (X.affineOpenCover.f i)).obj M).restrict
      (X.affineOpenCover.f i).isoOpensRange.inv).IsQuasicoherent := inferInstance
  exact Stacks.Descent.isQuasicoherent_of_iso
    (((Scheme.Modules.restrictFunctorComp (X.affineOpenCover.f i).isoOpensRange.inv
        (X.affineOpenCover.f i)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr
        (X.affineOpenCover.f i).isoOpensRange_inv_comp).app M) hres

/-! ### The affine case -/

/-- Isomorphisms in both arguments of the derived tensor product give an isomorphism of values. -/
private def tensorIsoCongr {X : Scheme.{u}} {A A' B B' : DerivedCategory X.Modules}
    (e : A ≅ A') (e' : B ≅ B') :
    ((derivedTensor X).obj A).obj B ≅ ((derivedTensor X).obj A').obj B' :=
  ((derivedTensor X).mapIso e).app B ≪≫ ((derivedTensor X).obj A').mapIso e'

/-- **[Stacks, Tag 08DX] part (1) on an affine scheme**, given [Stacks, Tag 08DX] part (2) in the
form in which it is used.

The hypothesis `hten` says that the derived tensor product of two derived sheafifications is
again a derived sheafification; part (2) supplies it, with the second factor named. Given it, the
affine case is [Stacks, Tag 06Z0]: derived sheafification is an equivalence onto
`D_QCoh(𝒪_{Spec R})`, so `K` and `L` are derived sheafifications of complexes of `R`-modules,
`hten` makes their derived tensor product one as well, and the cohomology sheaves of a derived
sheafification are quasi-coherent by construction. -/
theorem isQuasicoherent_homology_derivedTensor_spec (R : CommRingCat.{u})
    (hten : ∀ M N : DerivedCategory (ModuleCat.{u} R),
      ∃ W : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((((derivedTensor (Spec R)).obj ((derivedTildeFunctor R).obj M)).obj
          ((derivedTildeFunctor R).obj N)) ≅ (derivedTildeFunctor R).obj W))
    (K L : quasiCoherentDerivedCategory (Spec R)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      (((derivedTensor (Spec R)).obj K.obj).obj L.obj)).IsQuasicoherent := by
  have key : ∀ K : quasiCoherentDerivedCategory (Spec R),
      ∃ M, Nonempty ((derivedTildeFunctor R).obj M ≅ K.obj) := fun K => by
    obtain ⟨M, ⟨eM⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde R) K
    exact ⟨M, ⟨((derivedTildeCompι R).app M).symm ≪≫
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso eM⟩⟩
  obtain ⟨M, ⟨eK⟩⟩ := key K
  obtain ⟨N, ⟨eL⟩⟩ := key L
  obtain ⟨W, ⟨eW⟩⟩ := hten M N
  have e : ((derivedTensor (Spec R)).obj K.obj).obj L.obj ≅ (derivedTildeFunctor R).obj W :=
    tensorIsoCongr eK.symm eL.symm ≪≫ eW
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso e).symm
    (isQuasicoherent_homology_mapDerivedCategory_obj R W i)

/-! ### Derived sheafification and the derived tensor product on an affine scheme -/

/-- **Every object of `D(R)` is the class of a K-flat complex of `R`-modules.** This is the
existence of K-flat resolutions over a ring, packaged by
`CochainComplex.KFlat.chosenResolution`, together with the fact that a quasi-isomorphism becomes
invertible in the derived category. -/
theorem exists_kFlat_module_complex_iso (R : CommRingCat.{u})
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (M : DerivedCategory (ModuleCat.{u} R)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} P ∧
      Nonempty ((DerivedCategory.Q.obj P : DerivedCategory (ModuleCat.{u} R)) ≅ M) :=
  let res := CochainComplex.KFlat.chosenResolution.{u, u} (DerivedCategory.Q.objPreimage M)
  have := res.quasiIso
  ⟨res.complex, res.kFlat,
    ⟨asIso (DerivedCategory.Q.map res.π) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

/-- **On K-flat complexes, the derived tensor product of two derived sheafifications is the
derived sheafification of the ordinary total tensor complex.** For K-flat complexes `P` and `P'`
of `R`-modules,

`P̃ ⊗ᴸ_{𝒪_{Spec R}} P̃' ≅ (Tot(P ⊗_R P'))~`.

Reading the composite: derived sheafification of the class of a complex is the class of the
degreewise sheafification, by `CategoryTheory.Functor.mapDerivedCategoryFactors`; the
sheafification of a K-flat complex is K-flat ([Stacks, Tag 08DV],
`AlgebraicGeometry.kFlat_tilde`), so the `comparison` field of the derived tensor product on
`Spec R` computes the left-hand side as the class of `Tot(P̃ ⊗_{𝒪_{Spec R}} P̃')`; and that
complex is the sheafification of `Tot(P ⊗_R P')`, by the totalised affine tensor comparison
`AlgebraicGeometry.affineTensorComplexIso` of [Stacks, Tag 08DX] part (2). -/
def derivedTensorDerivedTildeIsoOfKFlat (R : CommRingCat.{u})
    (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P') :
    ((derivedTensor (Spec R)).obj
          ((derivedTildeFunctor R).obj (DerivedCategory.Q.obj P))).obj
        ((derivedTildeFunctor R).obj (DerivedCategory.Q.obj P')) ≅
      (derivedTildeFunctor R).obj (DerivedCategory.Q.obj (P ⊗ P')) :=
  ((derivedTensor (Spec R)).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P)).app _ ≪≫
    ((derivedTensor (Spec R)).obj
        (DerivedCategory.Q.obj (tildeComplexMod P))).mapIso
      ((tilde.functor R).mapDerivedCategoryFactors.app P') ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).comparison _ _
      (kFlat_tilde P hP) (kFlat_tilde P' hP') ≪≫
    DerivedCategory.Q.mapIso (affineTensorComplexIso R P P').1.symm ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app (P ⊗ P')).symm

/-- **The derived tensor product of two derived sheafifications is a derived sheafification.**
For `M, N` in `D(R)` there is an object `W` of `D(R)` and an isomorphism
`M̃ ⊗ᴸ_{𝒪_{Spec R}} Ñ ≅ W̃`.

Replace `M` and `N` by K-flat representatives `P` and `P'`; then
`derivedTensorDerivedTildeIsoOfKFlat` exhibits `W = Q(Tot(P ⊗_R P'))`.

This is weaker than [Stacks, Tag 08DX] part (2), which identifies the left-hand side with
`(M ⊗ᴸ_R N)~`; it is what the proof of part (1) consumes, and it carries no tag. -/
theorem exists_iso_derivedTilde_derivedTensor (R : CommRingCat.{u})
    (M N : DerivedCategory (ModuleCat.{u} R)) :
    ∃ W : DerivedCategory (ModuleCat.{u} R),
      Nonempty ((((derivedTensor (Spec R)).obj ((derivedTildeFunctor R).obj M)).obj
        ((derivedTildeFunctor R).obj N)) ≅ (derivedTildeFunctor R).obj W) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_module_complex_iso R M
  obtain ⟨P', hP', ⟨eP'⟩⟩ := exists_kFlat_module_complex_iso R N
  refine ⟨DerivedCategory.Q.obj (P ⊗ P'), ⟨?_⟩⟩
  exact tensorIsoCongr ((derivedTildeFunctor R).mapIso eP.symm)
      ((derivedTildeFunctor R).mapIso eP'.symm) ≪≫
    derivedTensorDerivedTildeIsoOfKFlat R P P' hP hP'

/-! ### Restriction along an open immersion -/

section Restriction

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]

/-- Degreewise pullback of a complex of `𝒪_Y`-modules along `g`, in the tensor spelling of the
two categories of sheaves of modules. -/
abbrev pullbackComplex (P : TensorComplex Y) : TensorComplex X :=
  ((StacksDraft.KFlat.modulePullback g.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- Pullback along an open immersion is left exact: it is restriction to an open, up to the
canonical isomorphism `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and
restriction to an open preserves finite limits. -/
instance preservesFiniteLimits_schemeModulesPullback_of_isOpenImmersion :
    PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback g)

omit [IsOpenImmersion g] in
/-- Pullback of sheaves of modules along a morphism of schemes is right exact, being a left
adjoint. The crossing between the scheme and ringed-space spellings of the functor is made here,
in term position, where the conversion check runs at default transparency. -/
@[ega "0 5.1.4" "special case"]
instance preservesFiniteColimits_schemeModulesPullback :
    PreservesFiniteColimits (Scheme.Modules.pullback g) :=
  have h : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  h

/-- **Pullback along an open immersion commutes with the cohomology of a complex**:
`g^*H^i(Q(C)) ≅ H^i(Q(g^*C))`. Pullback along `g` is exact, so it commutes with the cohomology of
the derived category (`AlgebraicGeometry.derivedHomologyMapIso`) and its derived functor is
degreewise pullback (`CategoryTheory.Functor.mapDerivedCategoryFactors`). -/
def pullbackHomologyQIso (C : TensorComplex Y) (i : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((DerivedCategory.homologyFunctor Y.Modules i).obj (DerivedCategory.Q.obj C)) ≅
      (DerivedCategory.homologyFunctor X.Modules i).obj
        (DerivedCategory.Q.obj (pullbackComplex g C)) :=
  derivedHomologyMapIso (Scheme.Modules.pullback g) (DerivedCategory.Q.obj C) i ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((Scheme.Modules.pullback g).mapDerivedCategoryFactors.app C)

omit [IsOpenImmersion g] in
/-- **The degreewise pullback of a K-flat complex is K-flat** ([Stacks, Tag 06YC]). -/
theorem kFlatComplex_pullbackComplex {P : TensorComplex Y} (hP : KFlatComplex P) :
    KFlatComplex (pullbackComplex g P) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional g.toLRSHom.toShHom P hP

/-- **The local computation.** For K-flat complexes `P` and `Q` of `𝒪_Y`-modules,

`g^*H^i(Q(Tot(P ⊗_{𝒪_Y} Q))) ≅ H^i(Q(g^*P) ⊗ᴸ_{𝒪_X} Q(g^*Q))`.

Reading the composite: pullback commutes with the cohomology of the class of a complex; the
pullback of a total tensor complex is the total tensor complex of the pullbacks, degreewise by
[Stacks, Tag 01CD]; and the pullbacks of `P` and `Q` are K-flat, so that total tensor complex
computes their derived tensor product. No statement about derived pullback is used. -/
def pullbackHomologyDerivedTensorIso (P Q : TensorComplex Y)
    (hP : KFlatComplex P) (hQ : KFlatComplex Q) (i : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((DerivedCategory.homologyFunctor Y.Modules i).obj
          (DerivedCategory.Q.obj (totalTensorComplex P Q))) ≅
      (DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensor X).obj (DerivedCategory.Q.obj (pullbackComplex g P))).obj
          (DerivedCategory.Q.obj (pullbackComplex g Q))) :=
  pullbackHomologyQIso g (totalTensorComplex P Q) i ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso
      (DerivedCategory.Q.mapIso
        (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso
          g.toLRSHom.toShHom P Q)) ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparison
        (pullbackComplex g P) (pullbackComplex g Q)
        (kFlatComplex_pullbackComplex g hP) (kFlatComplex_pullbackComplex g hQ)).symm

/-- **The pullback of a K-flat representative of an object of `D_QCoh(𝒪_Y)` lies in
`D_QCoh(𝒪_X)`.** Pullback commutes with the cohomology of the class of `P`, and pullback
preserves quasi-coherence ([Stacks, Tag 01BG]). -/
theorem isQuasicoherent_homology_Q_pullbackComplex (P : TensorComplex Y)
    (E : DerivedCategory Y.Modules)
    (eP : (DerivedCategory.Q.obj P : DerivedCategory Y.Modules) ≅ E)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj E).IsQuasicoherent)
    (j : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules j).obj
      (DerivedCategory.Q.obj (pullbackComplex g P))).IsQuasicoherent :=
  have hP : ((DerivedCategory.homologyFunctor Y.Modules j).obj
      (DerivedCategory.Q.obj P)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor Y.Modules j).mapIso eP).symm (hE j)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (pullbackHomologyQIso g P j) (Stacks.Modules.isQuasicoherent_pullback g _ hP)

end Restriction

/-! ### [Stacks, Tag 08DX] part (1) -/

/-- **[Stacks, Tag 08DX] part (1), given part (2) in the form in which it is used.** For an
arbitrary scheme `X` and objects `K, L` of `D_QCoh(𝒪_X)`, every cohomology sheaf of
`K ⊗ᴸ_{𝒪_X} L` is quasi-coherent.

The hypothesis `hten`, for each ring `R`, says that the derived tensor product on `Spec R` of two
derived sheafifications is again a derived sheafification; it is the only input that is not
proved here, and [Stacks, Tag 08DX] part (2) supplies it.

`K` and `L` are replaced by K-flat representatives `P` and `Q`, on which the derived tensor
product is `Q(Tot(P ⊗ Q))`. Quasi-coherence of the `i`-th cohomology sheaf of that is local, so
it suffices to prove it after restriction along each member `g : Spec R ⟶ X` of the affine open
cover; and there `pullbackHomologyDerivedTensorIso` identifies the restriction with the `i`-th
cohomology sheaf of `Q(g^*P) ⊗ᴸ Q(g^*Q)`, whose two factors lie in `D_QCoh(𝒪_{Spec R})` by
`isQuasicoherent_homology_Q_pullbackComplex`, so the affine case applies. -/
theorem isQuasicoherent_homology_derivedTensor_of_tensorTilde
    (hten : ∀ (R : CommRingCat.{u}) (M N : DerivedCategory (ModuleCat.{u} R)),
      ∃ W : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((((derivedTensor (Spec R)).obj ((derivedTildeFunctor R).obj M)).obj
          ((derivedTildeFunctor R).obj N)) ≅ (derivedTildeFunctor R).obj W))
    (X : Scheme.{u}) (K L : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedTensor X).obj K.obj).obj L.obj)).IsQuasicoherent := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlatComplex_iso X K.obj
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_kFlatComplex_iso X L.obj
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso
      (derivedTensorIsoQTensorComplex X K.obj L.obj P Q hP hQ eP eQ)).symm ?_
  refine isQuasicoherent_of_restrict_spec X _ fun R g _ => ?_
  refine (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app _).symm ?_
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (pullbackHomologyDerivedTensorIso g P Q hP hQ i).symm
    (isQuasicoherent_homology_derivedTensor_spec R (hten R)
      ⟨DerivedCategory.Q.obj (pullbackComplex g P),
        isQuasicoherent_homology_Q_pullbackComplex g P K.obj eP K.property⟩
      ⟨DerivedCategory.Q.obj (pullbackComplex g Q),
        isQuasicoherent_homology_Q_pullbackComplex g Q L.obj eQ L.property⟩ i)

/-- **[Stacks, Tag 08DX] part (1) as structure, given part (2).** The derived tensor product
restricts to a bifunctor `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X)`.

The uncurried derived tensor product, precomposed with the inclusion of `D_QCoh(𝒪_X)` in each
variable, lands in `D_QCoh(𝒪_X)` by `isQuasicoherent_homology_derivedTensor_of_tensorTilde`, so it
lifts to the full subcategory; currying the lift gives the bifunctor. -/
def quasiCoherentDerivedTensor_of_tensorTilde
    (hten : ∀ (R : CommRingCat.{u}) (M N : DerivedCategory (ModuleCat.{u} R)),
      ∃ W : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((((derivedTensor (Spec R)).obj ((derivedTildeFunctor R).obj M)).obj
          ((derivedTildeFunctor R).obj N)) ≅ (derivedTildeFunctor R).obj W))
    (X : Scheme.{u}) :
    quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory X ⥤
      quasiCoherentDerivedCategory X :=
  Functor.curryObj (ObjectProperty.lift
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    ((ObjectProperty.ι _).prod (ObjectProperty.ι _) ⋙ Functor.uncurry.obj (derivedTensor X))
    fun p i => isQuasicoherent_homology_derivedTensor_of_tensorTilde hten X p.1 p.2 i)

/-- The restricted bifunctor is a restriction: its value on `K` and `L` has underlying object
`K ⊗ᴸ_{𝒪_X} L`. -/
theorem quasiCoherentDerivedTensor_of_tensorTilde_obj_obj_obj
    (hten : ∀ (R : CommRingCat.{u}) (M N : DerivedCategory (ModuleCat.{u} R)),
      ∃ W : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((((derivedTensor (Spec R)).obj ((derivedTildeFunctor R).obj M)).obj
          ((derivedTildeFunctor R).obj N)) ≅ (derivedTildeFunctor R).obj W))
    (X : Scheme.{u}) (K L : quasiCoherentDerivedCategory X) :
    (((quasiCoherentDerivedTensor_of_tensorTilde hten X).obj K).obj L).obj =
      ((derivedTensor X).obj K.obj).obj L.obj :=
  rfl

/-! ### [Stacks, Tag 08DX] part (1), with no hypothesis -/

/-- **[Stacks, Tag 08DX] part (1): `D_QCoh(𝒪_X)` is closed under the derived tensor product.**
Let `X` be a scheme and let `K` and `L` be complexes of `𝒪_X`-modules all of whose cohomology
sheaves are quasi-coherent. Then every cohomology sheaf of `K ⊗ᴸ_{𝒪_X} L` is quasi-coherent.

This is `isQuasicoherent_homology_derivedTensor_of_tensorTilde` with its hypothesis discharged by
`exists_iso_derivedTilde_derivedTensor`. -/
@[stacks 08DX "part (1): D_QCoh is closed under derived tensor product"]
theorem isQuasicoherent_homology_derivedTensor (X : Scheme.{u})
    (K L : quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedTensor X).obj K.obj).obj L.obj)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedTensor_of_tensorTilde
    exists_iso_derivedTilde_derivedTensor X K L i

/-- **[Stacks, Tag 08DX] part (1), as structure: the derived tensor product restricts to
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_X)`.** This is
`quasiCoherentDerivedTensor_of_tensorTilde` with its hypothesis discharged by
`exists_iso_derivedTilde_derivedTensor`. -/
@[stacks 08DX "part (1): the restriction D_QCoh ⥤ D_QCoh ⥤ D_QCoh of the derived tensor product"]
abbrev quasiCoherentDerivedTensor (X : Scheme.{u}) :
    quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory X ⥤
      quasiCoherentDerivedCategory X :=
  quasiCoherentDerivedTensor_of_tensorTilde exists_iso_derivedTilde_derivedTensor X

/-- The restricted bifunctor is a restriction: its value on `K` and `L` has underlying object
`K ⊗ᴸ_{𝒪_X} L`. -/
theorem quasiCoherentDerivedTensor_obj_obj_obj (X : Scheme.{u})
    (K L : quasiCoherentDerivedCategory X) :
    (((quasiCoherentDerivedTensor X).obj K).obj L).obj =
      ((derivedTensor X).obj K.obj).obj L.obj :=
  rfl

end Stacks.Duality

end
