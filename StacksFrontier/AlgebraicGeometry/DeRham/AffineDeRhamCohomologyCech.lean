module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechClasses
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechMul
public import StacksFrontier.RingTheory.Kaehler.DeRhamShiftedSumHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ConcreteTotalTopCover
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary

/-!
# De Rham cohomology of an affine scheme over an affine base, with explicit classes

Let `g : Y ⟶ S` be a morphism of schemes with `Y` and `S` affine, and write `A = Γ(Y, 𝒪_Y)` and
`R = Γ(S, 𝒪_S)`. This file proves `H^k(Ω^•_{A/R}) ≅ H^k_{dR}(Y/S)` as `R`-modules, in every
degree `k : ℤ` ([Stacks, Tag 0FLW]), for the module realization
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyBaseModule` of de Rham cohomology, in which the
cup product `AlgebraicGeometry.Scheme.Hom.deRhamCup` lives, and with an explicit description of
the isomorphism on classes: a closed form `ν` of degree `b` goes to the Čech class, for the cover
of `Y` by `Y`, of the corresponding closed global section of `Ω^b_{Y/S}`. This is the form in
which the proof of [Stacks, Tag 0FUM] uses `H^*_{dR}(Y/S)`.

The library already proves Tag 0FLW for `Spec φ` in a third realization of de Rham cohomology
(`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamCohomologyIsoInt`); the statement here
is for an affine scheme `Y` itself and lands in the module realization, so that it composes with
the Čech description of classes and of cup products on `X` used for Tag 0FUM.

## Main definitions

* `AlgebraicGeometry.DeRhamKatzOdaCech.globalComplexIso`: `Ω^•_{A/R} ≅ Γ(Y, Ω^•_{Y/S})` as
  complexes of `R`-modules.
* `AlgebraicGeometry.DeRhamKatzOdaCech.affineClassComplexMap`: the map of complexes
  `Ω^•_{A/R} ⟶ Tot(Č({Y}, Ω^•_{Y/S}))` sending a form to the constant Čech `0`-cochain of the
  corresponding global section.
* `AlgebraicGeometry.DeRhamKatzOdaCech.affineClassMap`: the induced map
  `H^k(Ω^•_{A/R}) ⟶ H^k_{dR}(Y/S)`.
* `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamAffineIso`: **the isomorphism**
  `H^k(Ω^•_{A/R}) ≅ H^k_{dR}(Y/S)` of `R`-modules.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.bijective_affineClassMap`: the class map is bijective.
* `AlgebraicGeometry.DeRhamKatzOdaCech.cocycleClass_affineClassMap` and
  `AlgebraicGeometry.DeRhamKatzOdaCech.affineClassComplexMap_f`: the class of a cocycle of
  `Ω^•_{A/R}` goes to the Čech class of the constant cochain of the corresponding global form.

## Implementation notes

The proof is the Čech computation for the cover of `Y` by the single open `Y`: its total Čech
complex is homotopy equivalent to the complex of global sections
(`Stacks.CategoryTheory.CechComplex.TopCover.homotopyEquiv`), the Čech class map of an affine
cover of a scheme with affine diagonal is bijective
(`AlgebraicGeometry.DeRhamKatzOdaCech.bijective_classMap`), and the global sections of
`Ω^•_{Y/S}` are `Ω^•_{A/R}` (`AlgebraicGeometry.DeRhamKatzOdaCech.formsEquiv`).

The identification of complexes is assembled generically (`ringDeRhamIso`, for any ring map
`R ⟶ A` and any complex with semilinear identifications of its terms with the Kähler forms),
and only instantiated at the scheme level. Comparing, at the scheme level, two applications of
the identification of forms whose arguments differ only in the spelling of an instance makes
the unifier unfold that identification; with the generic construction no such comparison
arises. For the same reason the terms of the complex of global sections are read through
`globalSectionsEquiv`, whose source is spelled as the term of that complex.

## References

* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.AlgebraicGeometry.AffineDifferentialsIso (ringDeRhamComplex)

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section Generic

variable {R A : CommRingCat.{u}} (gR : R ⟶ A) (b : ℕ) {M : Type u} [AddCommGroup M] [Module R M]
  (e : M ≃+ ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
  (he : ∀ (r : R) (m : M), e (r • m) = gR r • e m)

/-- An additive identification of an `R`-module with the Kähler `b`-forms of `A/R`, semilinear
for `R ⟶ A`, as an `R`-linear identification with the degree-`b` term of `Ω^•_{A/R}`. -/
def ringFormsEquiv : M ≃ₗ[R] (ringDeRhamComplex gR).X b where
  toFun m := e m
  invFun ν := e.symm (Stacks.KatzOda.Cech.toForms gR ν)
  map_add' m m' := map_add e m m'
  map_smul' r m := he r m
  left_inv m := e.symm_apply_apply m
  right_inv ν := e.apply_symm_apply (Stacks.KatzOda.Cech.toForms gR ν)

include he in
/-- The Kähler form underlying `ringFormsEquiv gR b e he m` is `e m`. -/
theorem ringFormsEquiv_apply (m : M) :
    Stacks.KatzOda.Cech.toForms gR (ringFormsEquiv gR b e he m) = e m :=
  rfl

variable (K : CochainComplex (ModuleCat.{u} R) ℕ)
  (E : ∀ b, ↑(K.X b) ≃+ ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
  (hE : ∀ (b : ℕ) (r : R) (m : ↑(K.X b)), E b (r • m) = gR r • E b m)
  (hd : ∀ (b : ℕ) (m : ↑(K.X b)),
    E (b + 1) ((K.d b (b + 1)).hom m) = Stacks.KatzOda.dForms gR b (E b m))

/-- A complex of `R`-modules whose terms are identified with the Kähler forms of `A/R`,
semilinearly for `R ⟶ A` and compatibly with the differentials, is `Ω^•_{A/R}`. -/
def ringDeRhamIso : K ≅ ringDeRhamComplex gR :=
  HomologicalComplex.Hom.isoOfComponents
    (fun b => (ringFormsEquiv gR b (E b) (hE b)).toModuleIso) (by
      rintro b _ rfl
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      exact (hd b m).symm)

/-- The degree-`b` component of `ringDeRhamIso` sends `m` to the Kähler form `E b m`. -/
theorem ringDeRhamIso_hom_f_apply (b : ℕ) (m : ↑(K.X b)) :
    Stacks.KatzOda.Cech.toForms gR (((ringDeRhamIso gR K E hE hd).hom.f b).hom m) = E b m :=
  rfl

end Generic

variable {Y S : Scheme.{u}} (g : Y ⟶ S) [IsAffine Y] [IsAffine S]

/-- The terms of the complex of global sections of `Ω^•_{Y/S}` are the global sections of the
`Ω^b_{Y/S}`, read over `Γ(S, 𝒪_S)` through `g^♯`. -/
def globalSectionsEquiv (b : ℕ) :
    letI := baseModule g (Scheme.Hom.relativeDifferentialForms g (b : ℤ)) ⊤
    ↑((TopCover.globalComplex g.sectionsDeRhamComplex).X b) ≃ₗ[↑Γ(S, ⊤)]
      Γ(Scheme.Hom.relativeDifferentialForms g (b : ℤ), ⊤) :=
  letI := baseModule g (Scheme.Hom.relativeDifferentialForms g (b : ℤ)) ⊤
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The additive identification of global sections of `Ω^b_{Y/S}` with the Kähler forms
`Ω^b_{A/R}` of `A = Γ(Y, 𝒪_Y)` over `R = Γ(S, 𝒪_S)`. -/
def globalFormsAddEquiv (b : ℕ) :
    ↑((TopCover.globalComplex g.sectionsDeRhamComplex).X b) ≃+
      ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)) where
  toFun y := formsEquiv g (isAffineOpen_top Y) b (globalSectionsEquiv g b y)
  invFun ν := (globalSectionsEquiv g b).symm ((formsEquiv g (isAffineOpen_top Y) b).symm ν)
  left_inv y := by
    simp only [AddEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv ν := by
    simp only [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  map_add' y z := by
    simp only [map_add]

/-- `globalFormsAddEquiv` is `formsEquiv` applied after `globalSectionsEquiv`. -/
theorem globalFormsAddEquiv_apply (b : ℕ)
    (y : ↑((TopCover.globalComplex g.sectionsDeRhamComplex).X b)) :
    globalFormsAddEquiv g b y =
      formsEquiv g (isAffineOpen_top Y) b (globalSectionsEquiv g b y) := by
  simp only [globalFormsAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]

/-- `globalFormsAddEquiv` is semilinear for `baseMap g : Γ(S, 𝒪_S) ⟶ Γ(Y, 𝒪_Y)`. -/
theorem globalFormsAddEquiv_smul (b : ℕ) (r : Γ(S, ⊤))
    (y : ↑((TopCover.globalComplex g.sectionsDeRhamComplex).X b)) :
    globalFormsAddEquiv g b (r • y) = baseMap g r • globalFormsAddEquiv g b y := by
  let := baseModule g (Scheme.Hom.relativeDifferentialForms g (b : ℤ)) ⊤
  rw [globalFormsAddEquiv_apply, globalFormsAddEquiv_apply, map_smul]
  exact formsEquiv_smul g (isAffineOpen_top Y) b r _

/-- `globalFormsAddEquiv` intertwines the differential of the complex of global sections of
`Ω^•_{Y/S}` with the exterior derivative `Stacks.KatzOda.dForms` of Kähler forms. -/
theorem globalFormsAddEquiv_d (b : ℕ)
    (y : ↑((TopCover.globalComplex g.sectionsDeRhamComplex).X b)) :
    globalFormsAddEquiv g (b + 1)
        (((TopCover.globalComplex g.sectionsDeRhamComplex).d b (b + 1)).hom y) =
      Stacks.KatzOda.dForms (baseMap g) b (globalFormsAddEquiv g b y) := by
  rw [globalFormsAddEquiv_apply, globalFormsAddEquiv_apply]
  have h₁ : globalSectionsEquiv g (b + 1)
      (((TopCover.globalComplex g.sectionsDeRhamComplex).d b (b + 1)).hom y) =
      (g.deRhamComplex.d b (b + 1)).val.app (op ⊤) (globalSectionsEquiv g b y) := rfl
  rw [h₁]
  convert formsEquiv_d g (isAffineOpen_top Y) b (globalSectionsEquiv g b y) using 3

/-- **`Γ(Y, Ω^•_{Y/S}) = Ω^•_{A/R}`** for `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)` and
`R = Γ(S, 𝒪_S)`, as complexes of `R`-modules. -/
def globalComplexIso :
    ringDeRhamComplex (baseMap g) ≅ TopCover.globalComplex g.sectionsDeRhamComplex :=
  (ringDeRhamIso (baseMap g) (TopCover.globalComplex g.sectionsDeRhamComplex)
    (globalFormsAddEquiv g) (globalFormsAddEquiv_smul g) (globalFormsAddEquiv_d g)).symm

/-- The degree-`b` component of `globalComplexIso` sends a form `ν` to the global section of
`Ω^b_{Y/S}` corresponding to it under `formsEquiv`. -/
theorem globalComplexIso_hom_f_apply (b : ℕ) (ν : (ringDeRhamComplex (baseMap g)).X b) :
    ((globalComplexIso g).hom.f b).hom ν =
      (globalSectionsEquiv g b).symm ((formsEquiv g (isAffineOpen_top Y) b).symm
        (Stacks.KatzOda.Cech.toForms (baseMap g) ν)) :=
  rfl

/-! ### The classes -/

/-- The cover of `Y` by `Y`. -/
abbrev topCover : PUnit.{u + 1} → Y.Opens := TopCover.cover

omit [IsAffine Y] in
/-- The open `⊤` of `Y` is the union of the opens of `topCover`. -/
theorem top_eq_iSup_topCover : (⊤ : Y.Opens) = ⨆ i, topCover (Y := Y) i := by
  simp

/-- **The comparison of `Ω^•_{A/R}` with the total Čech complex of the cover `{Y}`**: a form is
sent to the constant Čech `0`-cochain of the corresponding global section of `Ω^•_{Y/S}`. -/
def affineClassComplexMap :
    Stacks.KatzOda.ShiftedSum.intComplex (baseMap g) ⟶ cechTot topCover g.sectionsDeRhamComplex :=
  HomologicalComplex.extendMap (globalComplexIso g).hom ComplexShape.embeddingUpNat ≫
    TopCover.incl g.sectionsDeRhamComplex

/-- **The degree-`b` component of `affineClassComplexMap`**: a form of degree `b` goes, through
`globalComplexIso`, to the corresponding global section of `Ω^b_{Y/S}`, and then to its constant
Čech `0`-cochain (`TopCover.inclX`), up to the canonical identifications of the terms in degree
`b` of the extended complexes. -/
theorem affineClassComplexMap_f (b : ℕ) :
    (affineClassComplexMap g).f b =
      ((ringDeRhamComplex (baseMap g)).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (globalComplexIso g).hom.f b ≫
          (TopCover.incl₀ g.sectionsDeRhamComplex).f b ≫
            ((cechTot topCover g.sectionsDeRhamComplex).restrictionXIso
              ComplexShape.embeddingUpNat rfl).hom := by
  have h : ComplexShape.embeddingUpNat.f b = (b : ℤ) := rfl
  rw [affineClassComplexMap, HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ h,
    TopCover.incl, ComplexShape.Embedding.descExtend_f _ h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- `affineClassComplexMap` induces isomorphisms on cohomology. -/
def affineHomologyIso (k : ℤ) :
    (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).homology k ≅
      (cechTot topCover g.sectionsDeRhamComplex).homology k :=
  HomologicalComplex.homologyMapIso
      ((ComplexShape.embeddingUpNat.extendFunctor _).mapIso (globalComplexIso g)) k ≪≫
    (TopCover.homotopyEquiv g.sectionsDeRhamComplex).symm.toHomologyIso k

/-- The forward map of `affineHomologyIso` is the map on cohomology induced by
`affineClassComplexMap`. -/
theorem affineHomologyIso_hom (k : ℤ) :
    (affineHomologyIso g k).hom = HomologicalComplex.homologyMap (affineClassComplexMap g) k := by
  rw [affineClassComplexMap, HomologicalComplex.homologyMap_comp]
  rfl

/-- **The class map `H^k(Ω^•_{A/R}) ⟶ H^k_{dR}(Y/S)`** for `Y` and `S` affine: the cohomology
of `affineClassComplexMap`, followed by the Čech class map of the cover `{Y}`. -/
def affineClassMap (k : ℤ) :
    (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).homology k ⟶
      Scheme.Hom.deRhamCohomologyBaseModule g k :=
  (affineHomologyIso g k).hom ≫ classMap g topCover top_eq_iSup_topCover k

/-- The class map `affineClassMap` is bijective. -/
theorem bijective_affineClassMap (k : ℤ) : Function.Bijective (affineClassMap g k).hom :=
  (bijective_classMap g topCover top_eq_iSup_topCover (fun _ => isAffineOpen_top Y) k).comp
    (ConcreteCategory.bijective_of_isIso (affineHomologyIso g k).hom)

/-- **The de Rham cohomology of an affine scheme over an affine base** ([Stacks, Tag 0FLW], in
the module realization of `H^*_{dR}`): for `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)` and
`R = Γ(S, 𝒪_S)`, `H^k(Ω^•_{A/R}) ≅ H^k_{dR}(Y/S)` as `R`-modules, by `affineClassMap`. -/
def deRhamAffineIso (k : ℤ) :
    (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).homology k ≅
      Scheme.Hom.deRhamCohomologyBaseModule g k :=
  (LinearEquiv.ofBijective (affineClassMap g k).hom (bijective_affineClassMap g k)).toModuleIso

/-- The forward map of `deRhamAffineIso` is `affineClassMap`. -/
theorem deRhamAffineIso_hom (k : ℤ) : (deRhamAffineIso g k).hom = affineClassMap g k :=
  rfl

open Stacks.Cech.Hypercohomology (cocycleClass cocycleClass_comp_homologyMap) in
/-- **The class of a cocycle**: the class in `H^k(Ω^•_{A/R})` of a cocycle `x` goes to the
Čech class of `affineClassComplexMap` applied to `x`, i.e. of the constant Čech `0`-cocycle of
the corresponding closed global form (`affineClassComplexMap_f`). -/
theorem cocycleClass_affineClassMap (k : ℤ) {M : ModuleCat.{u} Γ(S, ⊤)}
    (x : M ⟶ (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X k)
    (hx : x ≫ (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d k (k + 1) = 0) :
    cocycleClass k x hx ≫ affineClassMap g k =
      cocycleClass k (x ≫ (affineClassComplexMap g).f k)
          (by rw [Category.assoc, (affineClassComplexMap g).comm, reassoc_of% hx,
            Limits.zero_comp]) ≫
        classMap g topCover top_eq_iSup_topCover k := by
  rw [affineClassMap, affineHomologyIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (eq_whisker (cocycleClass_comp_homologyMap (affineClassComplexMap g) k x hx) _)

end AlgebraicGeometry.DeRhamKatzOdaCech

end
