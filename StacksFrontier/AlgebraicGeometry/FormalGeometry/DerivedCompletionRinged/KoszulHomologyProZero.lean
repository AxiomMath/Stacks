module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulConstantSystemAnnihilation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulCoefficientProIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pro-vanishing of the Koszul cohomology sheaves below the top degree

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `ℱ` be a sheaf
of `𝒪`-modules. `AlgebraicGeometry.RingedSite.koszulPowerComplexOn X f ℱ n` is the Koszul complex
on the `(n+1)`-st powers of the `f_i` with coefficients in `ℱ`, in the grading of
[Stacks, Tag 0913]: a complex of sheaves of `𝒪`-modules concentrated in the degrees `0, …, r`,
whose degree-`p` term is the product of copies of `ℱ` indexed by the subsets of `{1, …, r}` of
cardinality `p`, and whose top cohomology sheaf is `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`.

This file builds the transition map `koszulPowerComplexOnDown` from the `(m+1)`-st to the
`(n+1)`-st powers and proves that **the cohomology sheaves below the top degree are pro-zero**:
for every level `n` and every degree `p < r` there is a later level `m` at which the transition
induces the zero map `H^p` of sheaves. In the homological indexing of [Stacks, Tags 0A0E and
0A0K], where the Koszul complex sits in the degrees `-r, …, 0` and its degree-zero cohomology is
`ℱ/(f^{n+1})ℱ`, the degree `p` here is the degree `p - r`, so what is proved is the pro-vanishing
of `H^{-j}` for `j > 0`. In the grading used here `H^{-j}` for `j > 0` is identically zero,
because the complex is concentrated in the degrees `0, …, r`.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulPowerTransDownOn` and
  `AlgebraicGeometry.RingedSite.koszulPowerComplexOnDown` — the transition of Koszul systems and
  of Koszul complexes with coefficients, from the `(m+1)`-st down to the `(n+1)`-st powers, at a
  subset `S` multiplication by `f_{Sᶜ}^{m-n}`.
* `Stacks.KoszulProZero.modelSectionsFunctor` — the sections of a sheaf of `𝒪`-modules over an
  object `V`, read as modules over a model ring.
* `Stacks.KoszulProZero.rTensorModSystemIso` and `Stacks.KoszulProZero.coeffSystemIso` — the
  two isomorphisms of constant Koszul systems used to move the property between a model and its
  base change.

## Main results

* `Stacks.KoszulProZero.cocyclesIntoCoboundaries_of_iso` and
  `Stacks.KoszulProZero.cocyclesIntoCoboundaries_of_iso'` — the cocycle-into-coboundary property
  transports along isomorphisms of the complexes intertwining the maps.
* `Stacks.KoszulProZero.cocyclesIntoCoboundaries_rTensor` — **it passes along a flat base
  change**, because tensoring with a flat module is exact.
* `Stacks.KoszulProZero.cocyclesIntoCoboundaries_of_flat_model` — **the localization-stability
  of the Artin–Rees constant**: the property, at the level computed over a Noetherian model,
  holds for every flat base change of that model.
* `Stacks.KoszulProZero.homologyMap_eq_zero_of_local` and
  `Stacks.KoszulProZero.homologyMap_eq_zero_of_local_presieve` — **a map of complexes of sheaves
  of modules induces zero on a cohomology sheaf as soon as, over every object, it carries the
  sections killed by the differential into the image of the previous one after restriction along
  a covering family.** The target cohomology sheaf is separated, so a section killed locally is
  killed.
* `Stacks.KoszulProZero.cocyclesIntoCoboundaries_modelSectionsFunctor` — the property on the
  sections over an object carrying a model.
* `Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero` — **the main
  theorem**: under the hypothesis `hmodel`, for every level `n` and every degree `p < r` there is a
  later level `m` at which the downward Koszul transition induces the zero map on the degree-`p`
  cohomology *sheaf*.
* `Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_global` — the same
  with the model asked for over every object, the covering families being the identities.

Outside the degrees `0, …, r` there is nothing to prove:
`AlgebraicGeometry.RingedSite.isZero_homology_koszulPowerComplexOn_of_neg` and
`AlgebraicGeometry.RingedSite.isZero_homology_koszulPowerComplexOn_of_gt` of
`KoszulTopCohomologySheaf.lean` show the cohomology sheaves vanish there, and
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap` identifies the one in
degree `r` with `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`.

## Implementation notes

A pro-vanishing statement of this kind is false on a general ringed site — over a non-Noetherian
ring already the module-level statement fails — and the level `m` that works is not uniform over
the objects of the site unless something makes it so. The hypothesis used here, the argument
`hmodel` of the main theorem, is a **flat Noetherian model uniform over a basis**: a Noetherian
ring `A`, elements `a_1, …, a_r ∈ A` and a finite `A`-module `M` such that every object `U` of
`𝒞` admits a covering family of objects `V`, each carrying a ring map `A ⟶ 𝒪(V)` with
`a_i ↦ f_i|_V` and an identification of `ℱ(V)`, read as an `A`-module through that map, with the
base change `M ⊗_A S` of `M` along some flat `A`-module `S`.

The Artin–Rees constant, hence the level `m`, is computed **once**, over `A` and for `M`, and
inherited by every member of the covering family, because flatness makes the
cocycle-into-coboundary property pass along the base change. By contrast, the constant of
`Stacks.Algebraization.exists_artinRees_affineCover` is a `Finset.sup` over one chosen finite
affine cover, which controls no smaller open. No quasi-compactness is assumed: the uniformity
comes from the single model, not from a finite cover.

On the site of open subsets of an affine Noetherian scheme `Spec A`, with `ℱ` the
quasi-coherent sheaf of a finite `A`-module `M` and the `f_i` the sections of `a_i`, the
hypothesis holds with the covering families taken to be the standard opens `D(g) ⊆ U`: there
`𝒪(D(g)) = A_g` is flat over `A` and `ℱ(D(g)) = M ⊗_A A_g`, and the standard opens of an affine
form a basis. At `M = A` and `ℱ = 𝒪` it holds on the site of any scheme over `A` whose topology
is generated by opens whose sections are flat `A`-algebras.

For a coherent sheaf on a locally Noetherian scheme which is not globally the base change of
one finite module over one Noetherian ring, such a model exists only on each member of a finite
affine cover; finitely many models give one level by taking the maximum of their levels, which
is legitimate because the property persists at later levels, the composite of two downward
transitions being a downward transition.

On the site of open subsets of a scheme the hypothesis follows from the standard localization
statements: `AlgebraicGeometry.IsAffineOpen` and
`AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs` give that the sections of a
quasi-coherent module over a standard open `D(g)` of an affine open are the localization of the
sections over that affine open, `IsLocalizedModule.isBaseChange` turns a localization into a
base change, and a localization is flat.

The two Koszul systems in play, the one of sheaves of modules and the one of modules over the
model ring, are both constant systems whose transition maps are multiplication by a monomial, so
they are both instances of `CategoryTheory.AlternatingCech.constSystem` of
`KoszulConstantSystemAnnihilation.lean` — definitionally, which is what lets the Artin–Rees
input proved there for modules be used here for sheaves without any further comparison of
constructions. The functor taking sections over an object to modules over the model ring is
additive, hence preserves finite products, so it commutes with the alternating Čech complex by
`CategoryTheory.AlternatingCech.mapComplexIso`, compatibly with the transitions by
`CategoryTheory.AlternatingCech.mapComplexIso_hom_map`.

## References

* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AlternatingCech
open AlgebraicGeometry.RingedSite
open scoped TensorProduct

universe u v

namespace Stacks.KoszulProZero

/-! ## Transport of the cocycle-into-coboundary property -/

section Transport

variable {A : Type u} [CommRing A]

/-- **The cocycle-into-coboundary property transports along isomorphisms of the two complexes
which intertwine the two maps.** -/
theorem cocyclesIntoCoboundaries_of_iso
    {C D C' D' : CochainComplex (ModuleCat.{u} A) ℤ} (φ : C ⟶ D) (φ' : C' ⟶ D')
    (α : C ≅ C') (β : D ≅ D') (hcomm : α.hom ≫ φ' = φ ≫ β.hom) (p : ℤ)
    (h : CocyclesIntoCoboundaries φ p) : CocyclesIntoCoboundaries φ' p := by
  intro y hy
  have hcd : ∀ {K L : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ L) (i j : ℤ)
      (x : K.X i), (L.d i j).hom ((g.f i).hom x) = (g.f j).hom ((K.d i j).hom x) := by
    intro K L g i j x
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (g.comm i j)) x)
  have hyy : (α.hom.f p).hom ((α.inv.f p).hom y) = y := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f, α.inv_hom_id]
    rfl
  obtain ⟨z, hz⟩ := h _ (by rw [hcd α.inv, hy, map_zero])
  refine ⟨(β.hom.f (p - 1)).hom z, ?_⟩
  have h3 := congrArg (fun ψ : C ⟶ D' => (ψ.f p).hom ((α.inv.f p).hom y)) hcomm
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hyy] at h3
  rw [hcd β.hom, hz, h3]

/-- The same transport, with the two isomorphisms oriented the way the comparison of a functor
with the alternating Čech complex produces them. -/
theorem cocyclesIntoCoboundaries_of_iso'
    {C D C' D' : CochainComplex (ModuleCat.{u} A) ℤ} (φ : C ⟶ D) (φ' : C' ⟶ D')
    (α : C' ≅ C) (β : D' ≅ D) (hcomm : φ' ≫ β.hom = α.hom ≫ φ) (p : ℤ)
    (h : CocyclesIntoCoboundaries φ p) : CocyclesIntoCoboundaries φ' p := by
  refine cocyclesIntoCoboundaries_of_iso φ φ' α.symm β.symm ?_ p h
  change α.inv ≫ φ' = φ ≫ β.inv
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hcomm, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The cocycle-into-coboundary property passes along a flat base change.** Tensoring with a
flat module is exact, so a cocycle of the base-changed complex is the image of the base change of
the inclusion of the cocycles, and the base change of the coboundaries is the coboundaries. -/
theorem cocyclesIntoCoboundaries_rTensor (S : ModuleCat.{u} A) [Module.Flat A S]
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (φ : C ⟶ D) (p : ℤ)
    (h : CocyclesIntoCoboundaries φ p) :
    CocyclesIntoCoboundaries
      (((Stacks.KoszulCoefficientProIso.rTensorFunctor S).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) p := by
  intro y hy
  have hex : Function.Exact
      (LinearMap.ker ((C.d p (p + 1)).hom)).subtype ((C.d p (p + 1)).hom) :=
    LinearMap.exact_subtype_ker_map _
  have hy' : LinearMap.rTensor (S : Type u) ((C.d p (p + 1)).hom) y = 0 := hy
  obtain ⟨w, hw⟩ := (Module.Flat.rTensor_exact (S : Type u) hex y).1 hy'
  let ψ : (LinearMap.ker ((C.d p (p + 1)).hom)) →ₗ[A]
      (LinearMap.range ((D.d (p - 1) p)).hom) :=
    { toFun := fun z => ⟨(φ.f p).hom z.1, h z.1 (LinearMap.mem_ker.1 z.2)⟩
      map_add' := fun z z' => by ext; exact map_add _ _ _
      map_smul' := fun c z => by ext; exact map_smul _ _ _ }
  have hfact : ((φ.f p).hom) ∘ₗ (LinearMap.ker ((C.d p (p + 1)).hom)).subtype =
      (LinearMap.range ((D.d (p - 1) p)).hom).subtype ∘ₗ ψ := by
    ext z; rfl
  have hincl : (LinearMap.range ((D.d (p - 1) p)).hom).subtype ∘ₗ
      ((D.d (p - 1) p)).hom.rangeRestrict = ((D.d (p - 1) p)).hom := by
    ext u; rfl
  obtain ⟨v, hv⟩ := LinearMap.rTensor_surjective (S : Type u)
    (LinearMap.surjective_rangeRestrict ((D.d (p - 1) p)).hom) (LinearMap.rTensor S ψ w)
  refine ⟨v, ?_⟩
  change LinearMap.rTensor (S : Type u) ((D.d (p - 1) p)).hom v =
    LinearMap.rTensor (S : Type u) ((φ.f p).hom) y
  calc LinearMap.rTensor (S : Type u) ((D.d (p - 1) p)).hom v
      = LinearMap.rTensor (S : Type u)
          ((LinearMap.range ((D.d (p - 1) p)).hom).subtype)
          (LinearMap.rTensor (S : Type u) ((D.d (p - 1) p)).hom.rangeRestrict v) := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hincl]
    _ = LinearMap.rTensor (S : Type u)
          ((LinearMap.range ((D.d (p - 1) p)).hom).subtype)
          (LinearMap.rTensor (S : Type u) ψ w) := by rw [hv]
    _ = LinearMap.rTensor (S : Type u) ((φ.f p).hom) y := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← hfact, LinearMap.rTensor_comp,
          LinearMap.comp_apply, hw]

end Transport

/-! ## The Artin-Rees input over a flat base change of a Noetherian model -/

section FlatModel

open Stacks.KoszulCoefficientProIso (rTensorFunctor rTensorFunctor_map_smul_id)

variable {A : Type u} [CommRing A] {r : ℕ} (a : Fin r → A)

/-- The Artin–Rees input of
`Stacks.KoszulProZero.exists_modDown_cocyclesIntoCoboundaries`, stated for an arbitrary
multiplicative family of endomorphisms which happens to be monomial multiplication. -/
theorem exists_constDown_cocyclesIntoCoboundaries [IsNoetherianRing A] {N : ModuleCat.{u} A}
    [Module.Finite A N] (σ : (Fin r → ℕ) → (N ⟶ N)) (hσ0 : σ 0 = 𝟙 N)
    (hσadd : ∀ e e', σ e ≫ σ e' = σ (e + e')) (hσ : ∀ e, σ e = moduleKoszulValue a e • 𝟙 N)
    (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), CocyclesIntoCoboundaries (constDownMap σ hσ0 hσadd hnm) p := by
  have h : σ = smulFam a N := funext hσ
  subst h
  exact exists_modDown_cocyclesIntoCoboundaries a N n p hp

/-- **Tensoring the module Koszul system by a module is the module Koszul system of the tensor
product.** Both are constant systems whose transition maps are monomial multiplication, and
tensoring carries a scalar multiple of an identity to the same scalar multiple of an
identity. -/
def rTensorModSystemIso (M S : ModuleCat.{u} A) (n : ℕ) :
    modSystem a M n ⋙ rTensorFunctor S ≅ modSystem a ((rTensorFunctor S).obj M) n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro V W g
    change (rTensorFunctor S).map (smulFam a M (koszulExp n V W)) ≫ 𝟙 _ =
      𝟙 _ ≫ smulFam a ((rTensorFunctor S).obj M) (koszulExp n V W)
    rw [Category.comp_id, Category.id_comp]
    exact rTensorFunctor_map_smul_id S M _)

/-- **A coefficient isomorphism is an isomorphism of constant Koszul systems.** -/
def coeffSystemIso {N M' : ModuleCat.{u} A} (ε : N ≅ M')
    (σ : (Fin r → ℕ) → (N ⟶ N)) (hσ0 : σ 0 = 𝟙 N)
    (hσadd : ∀ e e', σ e ≫ σ e' = σ (e + e')) (hσ : ∀ e, σ e = moduleKoszulValue a e • 𝟙 N)
    (n : ℕ) : constSystem σ hσ0 hσadd n ≅ modSystem a M' n :=
  NatIso.ofComponents (fun _ => ε) (by
    intro V W g
    change σ (koszulExp n V W) ≫ ε.hom = ε.hom ≫ smulFam a M' (koszulExp n V W)
    rw [hσ]
    change (moduleKoszulValue a (koszulExp n V W) • 𝟙 N) ≫ ε.hom =
      ε.hom ≫ (moduleKoszulValue a (koszulExp n V W) • 𝟙 M')
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id])

/-- **The cocycle-into-coboundary property of the downward Koszul transition passes from a
Noetherian model to every flat base change of it.** The level `m` is the one computed over the
model, so it does not depend on the flat module: this is the localization-stability of the
Artin–Rees constant, and it is what makes a single level work simultaneously over a whole basis
of a site. -/
theorem cocyclesIntoCoboundaries_of_flat_model
    (M S : ModuleCat.{u} A) [Module.Flat A S]
    {N : ModuleCat.{u} A} (ε : N ≅ (rTensorFunctor S).obj M)
    (σ : (Fin r → ℕ) → (N ⟶ N)) (hσ0 : σ 0 = 𝟙 N)
    (hσadd : ∀ e e', σ e ≫ σ e' = σ (e + e')) (hσ : ∀ e, σ e = moduleKoszulValue a e • 𝟙 N)
    {m n : ℕ} (hnm : n ≤ m) (p : ℤ)
    (h : CocyclesIntoCoboundaries (modDown a M hnm) p) :
    CocyclesIntoCoboundaries (constDownMap σ hσ0 hσadd hnm) p := by
  have h1 := cocyclesIntoCoboundaries_rTensor S (modDown a M hnm) p h
  have hwhisk : Functor.whiskerRight
        (constDownNat (smulFam a M) (smulFam_zero a M) (smulFam_add a M) hnm)
        (rTensorFunctor S) ≫ (rTensorModSystemIso a M S n).hom =
      (rTensorModSystemIso a M S m).hom ≫
        constDownNat (smulFam a ((rTensorFunctor S).obj M))
          (smulFam_zero a ((rTensorFunctor S).obj M))
          (smulFam_add a ((rTensorFunctor S).obj M)) hnm := by
    refine NatTrans.ext (funext fun V => ?_)
    change (rTensorFunctor S).map (smulFam a M (downExp m n V)) ≫ 𝟙 _ =
      𝟙 _ ≫ smulFam a ((rTensorFunctor S).obj M) (downExp m n V)
    rw [Category.comp_id, Category.id_comp]
    exact rTensorFunctor_map_smul_id S M _
  have h2 := cocyclesIntoCoboundaries_of_iso
    (((rTensorFunctor S).mapHomologicalComplex (ComplexShape.up ℤ)).map (modDown a M hnm))
    (modDown a ((rTensorFunctor S).obj M) hnm)
    (mapComplexIso (rTensorFunctor S) (modSystem a M m) ≪≫ mapIso (rTensorModSystemIso a M S m))
    (mapComplexIso (rTensorFunctor S) (modSystem a M n) ≪≫ mapIso (rTensorModSystemIso a M S n))
    (mapComplexIso_trans_mapIso_map (rTensorFunctor S) _ _ _ _ hwhisk).symm p h1
  refine cocyclesIntoCoboundaries_of_iso _ _
    (mapIso (coeffSystemIso a ε σ hσ0 hσadd hσ m)).symm
    (mapIso (coeffSystemIso a ε σ hσ0 hσadd hσ n)).symm ?_ p h2
  change map (coeffSystemIso a ε σ hσ0 hσadd hσ m).inv ≫
      map (constDownNat σ hσ0 hσadd hnm) =
    map (constDownNat (smulFam a ((rTensorFunctor S).obj M))
        (smulFam_zero a ((rTensorFunctor S).obj M))
        (smulFam_add a ((rTensorFunctor S).obj M)) hnm) ≫
      map (coeffSystemIso a ε σ hσ0 hσadd hσ n).inv
  rw [← map_comp, ← map_comp]
  refine congrArg map (NatTrans.ext (funext fun V => ?_))
  change ε.inv ≫ σ (downExp m n V) =
    smulFam a ((rTensorFunctor S).obj M) (downExp m n V) ≫ ε.inv
  rw [hσ]
  change ε.inv ≫ (moduleKoszulValue a (downExp m n V) • 𝟙 N) =
    (moduleKoszulValue a (downExp m n V) • 𝟙 ((rTensorFunctor S).obj M)) ≫ ε.inv
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

end FlatModel

/-! ## The local criterion for the vanishing of a map of cohomology sheaves -/

section LocalCriterion

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A map of complexes of sheaves of modules induces the zero map on a cohomology sheaf as soon
as, over every object, it carries the sections killed by the differential into the image of the
previous differential after restriction along a covering sieve.**

This is what makes the vanishing of a map of cohomology *sheaves* checkable locally: the
cohomology sheaf of the target is a sheaf, hence separated, so a section of it which dies after
restriction along a covering sieve is already zero. No identification of the sections of a
cohomology sheaf with the cohomology of the sections is needed, and none holds in general: the
cohomology of a complex of sheaves of modules is a sheafification. -/
theorem homologyMap_eq_zero_of_local {K L : CochainComplex (SheafOfModules.{u} R) ℤ}
    (φ : K ⟶ L) (p : ℤ)
    (h : ∀ (U : Cᵒᵖ) (x : (K.X p).val.obj U), ((K.d p (p + 1)).val.app U) x = 0 →
      ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ ⦃V : C⦄ (g : V ⟶ U.unop), S g →
        ((L.X p).val.map g.op) (((φ.f p).val.app U) x) ∈
          LinearMap.range ((L.d (p - 1) p).val.app (op V)).hom) :
    HomologicalComplex.homologyMap φ p = 0 := by
  have hkey : K.iCycles p ≫ φ.f p ≫ L.pOpcycles p = 0 := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
    change ((L.pOpcycles p).val.app U) (((φ.f p).val.app U) (((K.iCycles p).val.app U) w)) = 0
    have hx : ((K.d p (p + 1)).val.app U) (((K.iCycles p).val.app U) w) = 0 :=
      congrArg (fun ψ : K.cycles p ⟶ K.X (p + 1) => (ψ.val.app U) w)
        (K.iCycles_d p (p + 1))
    obtain ⟨S, hS, hloc⟩ := h U _ hx
    refine Stacks.eq_of_isSeparated (L.opcycles p) hS (fun V g hg => ?_)
    obtain ⟨uu, hu⟩ := hloc g hg
    rw [map_zero, ← PresheafOfModules.naturality_apply (L.pOpcycles p).val g.op, ← hu]
    exact congrArg (fun ψ : L.X (p - 1) ⟶ L.opcycles p => (ψ.val.app (op V)) uu)
      (L.d_pOpcycles (p - 1) p)
  refine (cancel_mono (L.homologyι p)).1 ((cancel_epi (K.homologyπ p)).1 ?_)
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    HomologicalComplex.homology_π_ι, ← Category.assoc, HomologicalComplex.cyclesMap_i,
    Category.assoc, hkey]
  simp only [zero_comp, comp_zero]

/-- The same criterion with the local condition asked for only on the members of a covering
*presieve*: the condition is stable under further restriction, by the naturality of the
differential, so it propagates from a generating family to the sieve it generates. -/
theorem homologyMap_eq_zero_of_local_presieve {K L : CochainComplex (SheafOfModules.{u} R) ℤ}
    (φ : K ⟶ L) (p : ℤ)
    (h : ∀ (U : Cᵒᵖ) (x : (K.X p).val.obj U), ((K.d p (p + 1)).val.app U) x = 0 →
      ∃ P : Presieve U.unop, Sieve.generate P ∈ J U.unop ∧
        ∀ ⦃V : C⦄ (g : V ⟶ U.unop), P g →
          ((L.X p).val.map g.op) (((φ.f p).val.app U) x) ∈
            LinearMap.range ((L.d (p - 1) p).val.app (op V)).hom) :
    HomologicalComplex.homologyMap φ p = 0 := by
  refine homologyMap_eq_zero_of_local φ p (fun U x hx => ?_)
  obtain ⟨P, hP, hcond⟩ := h U x hx
  refine ⟨Sieve.generate P, hP, fun V g hg => ?_⟩
  obtain ⟨W, g₁, g₂, hg₂, hcomp⟩ := hg
  obtain ⟨uu, hu⟩ := hcond g₂ hg₂
  refine ⟨((L.X (p - 1)).val.map g₁.op) uu, ?_⟩
  rw [PresheafOfModules.naturality_apply (L.d (p - 1) p).val g₁.op, hu, ← hcomp]
  exact (PresheafOfModules.map_comp_apply (L.X p).val g₂.op g₁.op
    (((φ.f p).val.app U) x)).symm

end LocalCriterion

end Stacks.KoszulProZero

/-! ## The downward transition of the Koszul complexes with coefficients -/

namespace AlgebraicGeometry.RingedSite

section Down

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The map of systems from the `(m+1)`-st down to the `(n+1)`-st Koszul powers**, with
coefficients in `M`: at the subset `S` it is multiplication by `f_{Sᶜ}^{m-n}`. It is the
transition map of the inverse system of Koszul complexes, the one appearing in the Koszul formula
for the derived completion; `AlgebraicGeometry.RingedSite.koszulPowerTransOn` is the map in the
other direction. -/
def koszulPowerTransDownOn
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {m n : ℕ} (hnm : n ≤ m) :
    koszulPowerFunctorOn X f M m ⟶ koszulPowerFunctorOn X f M n :=
  AlternatingCech.constDownNat (fun e => koszulScalarOn X f e M) (koszulScalarOn_zero X f M)
    (fun e e' => koszulScalarOn_comp X f e e' M) hnm

/-- At the subset `S`, the downward map of systems is multiplication by the monomial with exponent
`AlternatingCech.downExp m n S`. -/
@[simp]
theorem koszulPowerTransDownOn_app
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) {m n : ℕ}
    (hnm : n ≤ m) (S : Finset (Fin r)) :
    (koszulPowerTransDownOn X f M hnm).app S =
      koszulScalarOn X f (AlternatingCech.downExp m n S) M :=
  rfl

/-- **The map `K(𝒪, f^{m+1}) ⊗ M ⟶ K(𝒪, f^{n+1}) ⊗ M` of Koszul complexes with coefficients**,
from the higher to the lower power. -/
def koszulPowerComplexOnDown
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {m n : ℕ} (hnm : n ≤ m) :
    koszulPowerComplexOn X f M m ⟶ koszulPowerComplexOn X f M n :=
  AlternatingCech.map (koszulPowerTransDownOn X f M hnm)

/-- The downward transition from a level to itself is the identity. -/
theorem koszulPowerComplexOnDown_self
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ) :
    koszulPowerComplexOnDown X f M (le_refl n) = 𝟙 (koszulPowerComplexOn X f M n) :=
  AlternatingCech.constDownMap_self _ _ _ n

/-- **The downward transitions compose**, so they form an inverse system. -/
theorem koszulPowerComplexOnDown_comp
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) {m₁ m₂ n : ℕ}
    (h₁ : m₁ ≤ m₂) (h₂ : n ≤ m₁) :
    koszulPowerComplexOnDown X f M h₁ ≫ koszulPowerComplexOnDown X f M h₂ =
      koszulPowerComplexOnDown X f M (h₂.trans h₁) :=
  AlternatingCech.constDownMap_comp _ _ _ h₁ h₂

end Down

end AlgebraicGeometry.RingedSite

/-! ## The main theorem -/

namespace Stacks.KoszulProZero

section Main

open Stacks.KoszulCoefficientProIso (rTensorFunctor)

variable (X : AlgebraicGeometry.RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The sections of a sheaf of `𝒪`-modules over an object `V`, read as modules over a model
ring** through a ring map from the model into `𝒪(V)`. -/
def modelSectionsFunctor {A : Type u} [CommRing A] (V : X.Cᵒᵖ)
    (ρ : A →+* (X.O.obj.obj V)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ ModuleCat.{u} A :=
  _root_.SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V ⋙
    ModuleCat.restrictScalars ρ

/-- The sections functor over `V`, with scalars restricted to the model ring, is additive. -/
instance additive_modelSectionsFunctor {A : Type u} [CommRing A] (V : X.Cᵒᵖ)
    (ρ : A →+* (X.O.obj.obj V)) : (modelSectionsFunctor X V ρ).Additive :=
  ⟨by intros; rfl⟩

/-- The monomial `∏_i f_i^{e_i}` acts on the sections over `V` as the model scalar
`∏_i a_i^{e_i}`, as soon as the model elements are carried to the given global sections. -/
theorem modelSectionsFunctor_map_koszulScalarOn {A : Type u} [CommRing A] (a : Fin r → A)
    (V : X.Cᵒᵖ) (ρ : A →+* (X.O.obj.obj V))
    (hρ : ∀ i, ρ (a i) = globalSectionVal (f i) V) (e : Fin r → ℕ) :
    (modelSectionsFunctor X V ρ).map (koszulScalarOn X f e ℱ) =
      moduleKoszulValue a e • 𝟙 ((modelSectionsFunctor X V ρ).obj ℱ) := by
  have hval : koszulValue X f e V = ρ (∏ i, a i ^ e i) := by
    rw [map_prod]
    change (∏ i, globalSectionVal (f i) V ^ e i) = ∏ i, ρ (a i ^ e i)
    exact Finset.prod_congr rfl fun i _ => by rw [map_pow, hρ i]
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : ℱ.val.obj V) => ?_)
  change koszulValue X f e V • x = ρ (∏ i, a i ^ e i) • x
  rw [hval]

/-- The monomial with zero exponent acts on the sections over `V` as the identity. -/
theorem modelSectionsFunctor_map_koszulScalarOn_zero {A : Type u} [CommRing A] (a : Fin r → A)
    (V : X.Cᵒᵖ) (ρ : A →+* (X.O.obj.obj V))
    (hρ : ∀ i, ρ (a i) = globalSectionVal (f i) V) :
    (modelSectionsFunctor X V ρ).map (koszulScalarOn X f 0 ℱ) =
      𝟙 ((modelSectionsFunctor X V ρ).obj ℱ) := by
  rw [modelSectionsFunctor_map_koszulScalarOn X f ℱ a V ρ hρ, moduleKoszulValue_zero, one_smul]

/-- On the sections over `V`, the action of `f^e` followed by that of `f^{e'}` is the action of
`f^{e+e'}`. -/
theorem modelSectionsFunctor_map_koszulScalarOn_comp {A : Type u} [CommRing A]
    (V : X.Cᵒᵖ) (ρ : A →+* (X.O.obj.obj V)) (e e' : Fin r → ℕ) :
    (modelSectionsFunctor X V ρ).map (koszulScalarOn X f e ℱ) ≫
        (modelSectionsFunctor X V ρ).map (koszulScalarOn X f e' ℱ) =
      (modelSectionsFunctor X V ρ).map (koszulScalarOn X f (e + e') ℱ) := by
  rw [← (modelSectionsFunctor X V ρ).map_comp, koszulScalarOn_comp]

/-- **Over an object carrying a flat Noetherian model, the downward Koszul transition carries the
cocycles of the sections into the coboundaries of the sections.** The level is the one computed
over the model, so it does not depend on the object: that is the uniformity the sheaf-level
statement needs. -/
theorem cocyclesIntoCoboundaries_modelSectionsFunctor {A : Type u} [CommRing A]
    (a : Fin r → A) (M S : ModuleCat.{u} A) [Module.Flat A S]
    (V : X.Cᵒᵖ) (ρ : A →+* (X.O.obj.obj V))
    (hρ : ∀ i, ρ (a i) = globalSectionVal (f i) V)
    (ε : (modelSectionsFunctor X V ρ).obj ℱ ≅ (rTensorFunctor S).obj M)
    {m n : ℕ} (hnm : n ≤ m) (p : ℤ)
    (h : CocyclesIntoCoboundaries (modDown a M hnm) p) :
    CocyclesIntoCoboundaries
      (((modelSectionsFunctor X V ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (koszulPowerComplexOnDown X f ℱ hnm)) p := by
  have h1 := cocyclesIntoCoboundaries_of_flat_model a M S ε
    (fun e => (modelSectionsFunctor X V ρ).map (koszulScalarOn X f e ℱ))
    (modelSectionsFunctor_map_koszulScalarOn_zero X f ℱ a V ρ hρ)
    (modelSectionsFunctor_map_koszulScalarOn_comp X f ℱ V ρ)
    (modelSectionsFunctor_map_koszulScalarOn X f ℱ a V ρ hρ) hnm p h
  have hbase := mapComplexIso_hom_map (modelSectionsFunctor X V ρ)
    (koszulPowerTransDownOn X f ℱ hnm)
  have hwhisk : map (Functor.whiskerRight (koszulPowerTransDownOn X f ℱ hnm)
        (modelSectionsFunctor X V ρ)) =
      constDownMap (fun e => (modelSectionsFunctor X V ρ).map (koszulScalarOn X f e ℱ))
        (modelSectionsFunctor_map_koszulScalarOn_zero X f ℱ a V ρ hρ)
        (modelSectionsFunctor_map_koszulScalarOn_comp X f ℱ V ρ) hnm :=
    congrArg map (NatTrans.ext (funext fun _ => rfl))
  rw [hwhisk] at hbase
  exact cocyclesIntoCoboundaries_of_iso' _ _
    (mapComplexIso (modelSectionsFunctor X V ρ) (koszulPowerFunctorOn X f ℱ m))
    (mapComplexIso (modelSectionsFunctor X V ρ) (koszulPowerFunctorOn X f ℱ n)) hbase p h1

/-- **The section-level form of the cocycle-into-coboundary property at an object.** Over `V`,
the downward Koszul transition carries the sections killed by the differential into the image of
the previous differential. This is the local datum from which the vanishing of the map of
cohomology *sheaves* is assembled, and it mentions no model. -/
def SectionsCocyclesIntoCoboundaries {m n : ℕ} (hnm : n ≤ m) (p : ℤ) (V : X.Cᵒᵖ) : Prop :=
  ∀ x : ((koszulPowerComplexOn X f ℱ m).X p).val.obj V,
    (((koszulPowerComplexOn X f ℱ m).d p (p + 1)).val.app V) x = 0 →
      (((koszulPowerComplexOnDown X f ℱ hnm).f p).val.app V) x ∈
        LinearMap.range (((koszulPowerComplexOn X f ℱ n).d (p - 1) p).val.app V).hom

/-- **A flat Noetherian model over an object, together with the Artin–Rees level computed over
the model, gives the section-level property over that object.** -/
theorem sectionsCocyclesIntoCoboundaries_of_model {A : Type u} [CommRing A]
    (a : Fin r → A) (M S : ModuleCat.{u} A) [Module.Flat A S]
    (V : X.Cᵒᵖ) (ρ : A →+* (X.O.obj.obj V))
    (hρ : ∀ i, ρ (a i) = globalSectionVal (f i) V)
    (ε : (modelSectionsFunctor X V ρ).obj ℱ ≅ (rTensorFunctor S).obj M)
    {m n : ℕ} (hnm : n ≤ m) (p : ℤ)
    (h : CocyclesIntoCoboundaries (modDown a M hnm) p) :
    SectionsCocyclesIntoCoboundaries X f ℱ hnm p V := by
  intro x hx
  obtain ⟨w, hw⟩ :=
    cocyclesIntoCoboundaries_modelSectionsFunctor X f ℱ a M S V ρ hρ ε hnm p h x hx
  exact ⟨w, hw⟩

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The downward Koszul transition induces the zero map on a cohomology sheaf as soon as the
section-level property holds over a covering family of every object.** -/
theorem homologyMap_eq_zero_of_sections {m n : ℕ} (hnm : n ≤ m) (p : ℤ)
    (h : ∀ U : X.Cᵒᵖ, ∃ P : Presieve U.unop, Sieve.generate P ∈ X.J U.unop ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U.unop), P g →
        SectionsCocyclesIntoCoboundaries X f ℱ hnm p (op V)) :
    HomologicalComplex.homologyMap (koszulPowerComplexOnDown X f ℱ hnm) p = 0 := by
  refine homologyMap_eq_zero_of_local_presieve _ p (fun U x hx => ?_)
  obtain ⟨P, hP, hsec⟩ := h U
  refine ⟨P, hP, fun V g hg => ?_⟩
  have hx' : (((koszulPowerComplexOn X f ℱ m).d p (p + 1)).val.app (op U.unop)) x = 0 := hx
  have hxV : ((koszulPowerComplexOn X f ℱ m).d p (p + 1)).val.app (op V)
      (((koszulPowerComplexOn X f ℱ m).X p).val.map g.op x) = 0 := by
    rw [PresheafOfModules.naturality_apply
      ((koszulPowerComplexOn X f ℱ m).d p (p + 1)).val g.op x, hx']
    exact map_zero _
  obtain ⟨w, hw⟩ := hsec g hg (((koszulPowerComplexOn X f ℱ m).X p).val.map g.op x) hxV
  exact ⟨w, hw.trans (PresheafOfModules.naturality_apply
    ((koszulPowerComplexOnDown X f ℱ hnm).f p).val g.op x)⟩

/-- **Pro-vanishing of the Koszul cohomology sheaves below the top degree.**

Let `(𝒞, 𝒪)` be a ringed site, `f_1, …, f_r` global sections of `𝒪` and `ℱ` a sheaf of
`𝒪`-modules. Suppose the Koszul data has a *flat Noetherian model uniform over a basis*: a
Noetherian ring `A`, elements `a_1, …, a_r ∈ A` and a finite `A`-module `M` such that every
object of `𝒞` is covered by objects `V` over which `𝒪(V)` is an `A`-algebra carrying `a_i` to
`f_i|_V` and `ℱ(V)` is the base change `M ⊗_A S` of `M` along a flat `A`-module `S`.

Then for every level `n` and every degree `p` below the top degree `r` there is a later level `m`
at which the downward Koszul transition induces the **zero map of cohomology sheaves** in degree
`p`. Since the Koszul complex is concentrated in the degrees `0, …, r` and its top cohomology
sheaf is `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`, this is the pro-vanishing of every cohomology sheaf
other than that quotient — in the homological indexing of [Stacks, Tags 0A0E and 0A0K], the
pro-vanishing of `H^{-j}` for `j > 0`.

The level `m` is uniform over the basis because it is computed once over the model and inherited
by each `V` through the flat base change; that is the step a constant obtained as a `Finset.sup`
over one chosen finite cover does not provide. -/
@[sga "2 II Lemma11" "partial"]
theorem exists_koszulPowerComplexOnDown_homologyMap_eq_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Fin r → A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hmodel : ∀ U : X.Cᵒᵖ, ∃ P : Presieve U.unop, Sieve.generate P ∈ X.J U.unop ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U.unop), P g →
        ∃ (ρ : A →+* (X.O.obj.obj (op V))) (S : ModuleCat.{u} A),
          (∀ i, ρ (a i) = globalSectionVal (f i) (op V)) ∧ Module.Flat A S ∧
            Nonempty ((modelSectionsFunctor X (op V) ρ).obj ℱ ≅ (rTensorFunctor S).obj M))
    (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      (koszulPowerComplexOnDown X f ℱ hnm) p = 0 := by
  obtain ⟨m, hnm, hmod⟩ := exists_modDown_cocyclesIntoCoboundaries a M n p hp
  refine ⟨m, hnm, homologyMap_eq_zero_of_sections X f ℱ hnm p (fun U => ?_)⟩
  obtain ⟨P, hP, hdata⟩ := hmodel U
  refine ⟨P, hP, fun V g hg => ?_⟩
  obtain ⟨ρ, S, hρ, hflat, ⟨ε⟩⟩ := hdata g hg
  have hfl := hflat
  exact sectionsCocyclesIntoCoboundaries_of_model X f ℱ a M S (op V) ρ hρ ε hnm p hmod

/-- **Pro-vanishing of the Koszul cohomology sheaves below the top degree, when the model is
available over every object.** This is the main theorem with the covering families taken to be
the identities, which the topology always covers with; it is the form in which the hypothesis is
easiest to check when the whole site is built over one Noetherian base. -/
theorem exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_global
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Fin r → A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hmodel : ∀ V : X.Cᵒᵖ, ∃ (ρ : A →+* (X.O.obj.obj V)) (S : ModuleCat.{u} A),
      (∀ i, ρ (a i) = globalSectionVal (f i) V) ∧ Module.Flat A S ∧
        Nonempty ((modelSectionsFunctor X V ρ).obj ℱ ≅ (rTensorFunctor S).obj M))
    (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      (koszulPowerComplexOnDown X f ℱ hnm) p = 0 := by
  refine exists_koszulPowerComplexOnDown_homologyMap_eq_zero X f ℱ A a M (fun U => ?_) n p hp
  refine ⟨Presieve.singleton (𝟙 U.unop), ?_, fun V g hg => ?_⟩
  · refine X.J.superset_covering ?_ (X.J.top_mem U.unop)
    intro W h _
    exact ⟨U.unop, h, 𝟙 U.unop, Presieve.singleton_self _, by simp⟩
  · cases hg
    exact hmodel (op U.unop)

end Main

end Stacks.KoszulProZero

end
