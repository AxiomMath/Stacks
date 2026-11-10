module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechSliceRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratedIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsDerivedLimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedCompletion

/-!
# Global sections of the Koszul complex with coefficients, at an arbitrary number of sections

Let `(𝒞, 𝒪)` be a ringed site, let `A` be a commutative ring, let `ρ : A ⟶ Γ(𝒞, 𝒪)` be a ring
map and let `a_1, …, a_r ∈ A`. Write `f_i` for the global section `ρ (a_i)` of `𝒪`. For a sheaf
of `𝒪`-modules `M` the *Koszul complex with coefficients in `M`* on the `(n+1)`-st powers of
`f_1, …, f_r` is the alternating Čech complex of the system `S ↦ M` indexed by the subsets of
`{1, …, r}`, whose transition map along `S ⊆ T` is multiplication by `∏_{i ∈ T ∖ S} f_i^{n+1}`.
At `M = 𝒪` it is `AlgebraicGeometry.RingedSite.koszulPowerComplex`, the Koszul complex of
[Stacks, Tag 0913] used in the Koszul formula [Stacks, Tag 0A0E].

This file proves that `A`-linear global sections carry that complex to the Koszul complex on
`a_1^{n+1}, …, a_r^{n+1}` with coefficients in the `A`-module `Γ(𝒞, M)`, compatibly with the
transition maps of the tower — that is, as an isomorphism of inverse systems of complexes of
`A`-modules. This is the degreewise content, read at global sections and at an arbitrary number
`r` of sections, of the projection formula [Stacks, Tag 0944] against the Koszul complexes, which
the proof of [Stacks, Tag 0A0G] invokes on the way to the identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of
[Stacks, Tag 0BLX].

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulPowerFunctorOn` and
  `AlgebraicGeometry.RingedSite.koszulPowerComplexOn`: the Koszul complex with coefficients in a
  sheaf of modules, which at the structure sheaf is
  `AlgebraicGeometry.RingedSite.koszulPowerComplex`.
* `AlgebraicGeometry.RingedSite.koszulPowerSystemOn`: the tower of those complexes.
* `AlgebraicGeometry.RingedSite.moduleKoszulPowerFunctor` and
  `AlgebraicGeometry.RingedSite.moduleKoszulPowerSystem`: the same construction for a module over
  a commutative ring, which is the Koszul complex on `a_1^{n+1}, …, a_r^{n+1}` with coefficients
  in that module.

## Main results

* `CategoryTheory.AlternatingCech.mapComplexIso_hom_map` and
  `CategoryTheory.AlternatingCech.mapComplexIso_trans_mapIso_map`: the comparison
  `G(Č(F)) ≅ Č(F ⋙ G)` of `CechBaseChange.lean`, for an additive, finite-product-preserving
  functor `G`, is compatible with the morphisms of alternating Čech complexes induced by a
  morphism of systems. This is what makes such a functor commute with a whole *tower* of Koszul
  complexes rather than with each of them separately.
* `AlgebraicGeometry.RingedSite.koszulPowerFunctorOn_unit`: the coefficient construction
  generalizes `AlgebraicGeometry.RingedSite.koszulPowerFunctor`, agreeing with it at the
  structure sheaf.
* `AlgebraicGeometry.RingedSite.globalSectionsKoszulPowerComplexIso`: **`A`-linear global
  sections carry the Koszul complex with coefficients in `M` on the `(n+1)`-st powers of
  `ρ a_1, …, ρ a_r` to the Koszul complex with coefficients in `Γ(𝒞, M)` on the `(n+1)`-st powers
  of `a_1, …, a_r`.**
* `AlgebraicGeometry.RingedSite.globalSectionsKoszulPowerSystemIso`: the same as an isomorphism
  of towers, that is of functors `ℕ ⥤ CochainComplex (ModuleCat A) ℤ`.

## Implementation notes

The statements here are about complexes, while the tower of the Koszul formula
[Stacks, Tag 0A0E] —
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_completion`
of `KoszulPerfectDual.lean` — is `n ↦ K ⊗^𝐋_𝒪 (K^n)^∨` in `D(𝒪)`. Two identifications connect
the two:

* `AlgebraicGeometry.RingedSite.koszulDualComplexIsoCoeff` of
  `KoszulDualCoefficientComplex.lean` identifies the derived tensor product with the Koszul
  complex with coefficients, through the internal Hom complex: the tower is rewritten as
  `n ↦ R𝑆heafHom_𝒪(K^n, ℱ)` by `AlgebraicGeometry.RingedSite.koszulTensorDualSystemIso`,
  represented by the internal Hom complexes by [Stacks, Tag 08JH], and those are identified with
  the Koszul complexes with coefficients. That identification carries a **shift by `r`**, because
  `(K^n)^∨` lives in degrees `-r, …, 0` and `koszulPowerComplexOn` in degrees `0, …, r`, and the
  resulting tower is the *inverse* system `AlgebraicGeometry.RingedSite.koszulDualSystemOn`, whose
  transition multiplies the factor indexed by `T` by `∏_{i ∉ T} f_i`, and not the direct system
  `AlgebraicGeometry.RingedSite.koszulPowerSystemOn` below. The assembled statement is
  `AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso`. The comparison
  `AlgebraicGeometry.RingedSite.tensorTotalKFlatComparison` does not apply here: it needs the
  **left** tensor factor to be K-flat, and the coefficient sheaf is arbitrary.
* `KoszulKFlat.lean` proves that `Γ(𝒞, -)` computes `RΓ(𝒞, -)` on the internal Hom complexes
  against the Koszul tower, at an arbitrary `r`.

No declaration here carries a `@[stacks]` attribute: [Stacks, Tag 0944] is a statement about
`Rf_*` and a perfect complex in the derived category, and what is proved here is the underlying
degreewise identity.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' v v' w

namespace CategoryTheory.AlternatingCech

/-! ## The comparison of alternating Čech complexes along a functor, on a tower

`CategoryTheory.AlternatingCech.mapComplexIso` of `ExtendedCechFunctoriality.lean` says that an
additive, finite-product-preserving functor `G` commutes with the extended alternating Čech
complex. The two statements here say that it does so compatibly with the morphisms induced by
morphisms of
systems, which is what makes it an isomorphism of *towers* of alternating Čech complexes rather
than of each of them separately. -/

section Square

variable {r : ℕ} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]
  {ℬ : Type u'} [Category.{v'} ℬ] [Preadditive ℬ] [HasFiniteProducts ℬ]
  (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteProducts G]

/-- **The comparison `G(Č(F)) ≅ Č(F ⋙ G)` is compatible with the morphism of alternating Čech
complexes induced by a morphism of systems.** Degreewise both sides are a projection followed by
the image of a component of the morphism. -/
theorem mapComplexIso_hom_map {F F' : Finset (Fin r) ⥤ 𝒜} (α : F ⟶ F') :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (map α) ≫ (mapComplexIso G F').hom =
      (mapComplexIso G F).hom ≫ map (Functor.whiskerRight α G) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  change G.map (mapX α p) ≫ (mapTermIso G F' p).hom =
    (mapTermIso G F p).hom ≫ mapX (Functor.whiskerRight α G) p
  refine Pi.hom_ext _ _ fun A => ?_
  rw [Category.assoc, mapTermIso_hom_comp_pi, ← G.map_comp, mapX_comp_pi, Category.assoc,
    mapX_comp_pi, ← Category.assoc, mapTermIso_hom_comp_pi, Functor.whiskerRight_app,
    ← G.map_comp]

/-- **One step of a tower, transported.** Suppose the image under `G` of each of two systems in
`𝒜` is identified with a system in `ℬ`, compatibly with a given morphism between the two systems.
Then the composite comparison — `G` commuting with the alternating Čech complex, followed by the
chosen identification — is compatible with the induced morphisms of alternating Čech complexes.
This is the square that makes the composite comparison an isomorphism of towers. -/
theorem mapComplexIso_trans_mapIso_map {F F' : Finset (Fin r) ⥤ 𝒜}
    {H H' : Finset (Fin r) ⥤ ℬ} (α : F ⟶ F') (eF : F ⋙ G ≅ H) (eF' : F' ⋙ G ≅ H')
    (β : H ⟶ H') (hcomm : Functor.whiskerRight α G ≫ eF'.hom = eF.hom ≫ β) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (map α) ≫
        (mapComplexIso G F' ≪≫ mapIso eF').hom =
      (mapComplexIso G F ≪≫ mapIso eF).hom ≫ map β := by
  rw [Iso.trans_hom, Iso.trans_hom, mapIso_hom, mapIso_hom, ← Category.assoc,
    mapComplexIso_hom_map, Category.assoc, Category.assoc, ← map_comp, ← map_comp, hcomm]

end Square

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative


/-! ## The exponent bookkeeping, shared by the sheaf and the module side -/

section Exponents

variable {r : ℕ}

/-- The exponent vector of a transition map along an identity inclusion is zero. -/
theorem koszulExp_self (n : ℕ) (S : Finset (Fin r)) : koszulExp n S S = 0 :=
  funext fun i => by simp [koszulExp]

/-- **The exponent vectors of the Koszul transition maps add along a composite inclusion.** This
is the combinatorial identity behind the functoriality of the Koszul system, and it is the same
one on the sheaf and on the module side. -/
theorem koszulExp_add {n : ℕ} {S T V : Finset (Fin r)} (hST : S ⊆ T) (hTV : T ⊆ V) :
    koszulExp n S V = koszulExp n S T + koszulExp n T V := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiS : i ∈ S <;>
      simp [koszulExp, hiT, hiS, hTV hiT, Finset.mem_sdiff, Pi.add_apply]
  · by_cases hiV : i ∈ V <;>
      simp [koszulExp, hiT, hiV, Finset.mem_sdiff, Pi.add_apply,
        show i ∉ S from fun hiS => hiT (hST hiS)]

/-- **The exponent identity behind the map from the `(n+1)`-st to the `(n+2)`-nd Koszul
powers**: `f_{T ∖ S}^{n+1} · f_T = f_S · f_{T ∖ S}^{n+2}` for `S ⊆ T`. -/
theorem koszulExp_add_indicator {n : ℕ} {S T : Finset (Fin r)} (hST : S ⊆ T) :
    koszulExp n S T + (fun i => if i ∈ T then 1 else 0) =
      (fun i => if i ∈ S then 1 else 0) + koszulExp (n + 1) S T := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiS : i ∈ S <;> simp [koszulExp, hiT, hiS, Finset.mem_sdiff, Pi.add_apply]
  · simp [koszulExp, hiT, Finset.mem_sdiff, Pi.add_apply,
      show i ∉ S from fun hiS => hiT (hST hiS)]

end Exponents

/-! ## The Koszul complex with coefficients in a sheaf of modules -/

section Coefficients

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Multiplication by the monomial `∏_i f_i^{e_i}` on a sheaf of `𝒪`-modules.** At the
structure sheaf this is `AlgebraicGeometry.RingedSite.koszulScalar`. -/
def koszulScalarOn (e : Fin r → ℕ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : M ⟶ M :=
  (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (koszulFamily X f e)).asHom.app M

/-- On sections over `U`, `koszulScalarOn` is scalar multiplication by `∏_i f_i^{e_i}`. -/
theorem koszulScalarOn_app (e : Fin r → ℕ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
    (x : M.val.obj U) :
    (koszulScalarOn X f e M).val.app U x = koszulRingValue X f e U • x :=
  rfl

/-- Two morphisms of sheaves of `𝒪`-modules agreeing on all sections over all objects are equal. -/
private theorem sheafOfModules_hom_ext_apply
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {g g' : M ⟶ N}
    (h : ∀ (U : X.Cᵒᵖ) (x : M.val.obj U), g.val.app U x = g'.val.app U x) : g = g' :=
  SheafOfModules.hom_ext <|
    PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext (h U))

/-- Composing multiplications adds exponents. -/
theorem koszulScalarOn_comp (e e' : Fin r → ℕ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    koszulScalarOn X f e M ≫ koszulScalarOn X f e' M = koszulScalarOn X f (e + e') M := by
  refine sheafOfModules_hom_ext_apply X fun U x => ?_
  change koszulRingValue X f e' U • (koszulRingValue X f e U • x) =
    koszulRingValue X f (e + e') U • x
  rw [← mul_smul]
  exact congrArg (fun c : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U => c • x)
    (koszulValue_mul_comm X f e e' U)

/-- Multiplication by the empty monomial is the identity. -/
theorem koszulScalarOn_zero (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    koszulScalarOn X f 0 M = 𝟙 M := by
  refine sheafOfModules_hom_ext_apply X fun U x => ?_
  change koszulRingValue X f 0 U • x = x
  rw [show koszulRingValue X f 0 U = 1 from koszulValue_zero X f U]
  exact one_smul _ x

/-- Multiplication depends on the exponent vector only through its values. -/
theorem koszulScalarOn_congr {e e' : Fin r → ℕ} (h : ∀ i, e i = e' i)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    koszulScalarOn X f e M = koszulScalarOn X f e' M := by
  rw [funext h]

/-- **The system of copies of `M` underlying the Koszul complex with coefficients in `M`**: the
constant system `S ↦ M` on the poset of subsets of `Fin r`, whose transition map along `S ⊆ T` is
multiplication by `f_{T ∖ S}^{n+1}`. At `M = 𝒪` it is
`AlgebraicGeometry.RingedSite.koszulPowerFunctor`. -/
def koszulPowerFunctorOn
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  obj _ := M
  map {S T} g := koszulScalarOn X f (koszulExp n S T) M
  map_id S := by
    rw [koszulExp_self]
    exact koszulScalarOn_zero X f M
  map_comp {S T V} g g' := by
    rw [koszulScalarOn_comp, koszulExp_add (leOfHom g) (leOfHom g')]

/-- The coefficient construction generalizes the Koszul complex of
[Stacks, Tag 0913]: at the structure sheaf it is
`AlgebraicGeometry.RingedSite.koszulPowerFunctor`. -/
theorem koszulPowerFunctorOn_unit (n : ℕ) :
    koszulPowerFunctorOn X f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n =
      koszulPowerFunctor X f n :=
  rfl

/-- **The Koszul complex `K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ M` with coefficients in `M`**, in the
grading of [Stacks, Tag 0913]: the term in degree `p` is the product of copies of `M` indexed by
the subsets of `{1, …, r}` of cardinality `p`. -/
def koszulPowerComplexOn
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  AlternatingCech.complex (koszulPowerFunctorOn X f M n)

/-- With coefficients in the structure sheaf, `koszulPowerComplexOn` is `koszulPowerComplex`. -/
theorem koszulPowerComplexOn_unit (n : ℕ) :
    koszulPowerComplexOn X f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n =
      koszulPowerComplex X f n :=
  rfl

/-- **The map of systems from the `(n+1)`-st to the `(n+2)`-nd Koszul powers**, with coefficients
in `M`: at the subset `S` it is multiplication by `f_S`. -/
def koszulPowerTransOn
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    koszulPowerFunctorOn X f M n ⟶ koszulPowerFunctorOn X f M (n + 1) where
  app S := koszulScalarOn X f (fun i => if i ∈ S then 1 else 0) M
  naturality {S T} g := by
    change koszulScalarOn X f (koszulExp n S T) M ≫ koszulScalarOn X f _ M =
      koszulScalarOn X f _ M ≫ koszulScalarOn X f (koszulExp (n + 1) S T) M
    rw [koszulScalarOn_comp, koszulScalarOn_comp, koszulExp_add_indicator (leOfHom g)]

/-- The map `K(𝒪, f^{n+1}) ⊗ M ⟶ K(𝒪, f^{n+2}) ⊗ M` of Koszul complexes with coefficients. -/
def koszulPowerComplexOnMap
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    koszulPowerComplexOn X f M n ⟶ koszulPowerComplexOn X f M (n + 1) :=
  AlternatingCech.map (koszulPowerTransOn X f M n)

/-- **The tower of Koszul complexes with coefficients in `M`** on the positive powers of
`f_1, …, f_r`. The index `n` carries the exponent `n + 1`. -/
def koszulPowerSystemOn (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Functor.ofSequence (koszulPowerComplexOnMap X f M)

/-- The `n`-th term of `koszulPowerSystemOn` is `koszulPowerComplexOn X f M n`. -/
@[simp]
theorem koszulPowerSystemOn_obj
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    (koszulPowerSystemOn X f M).obj n = koszulPowerComplexOn X f M n :=
  rfl

end Coefficients

/-! ## The Koszul complex with coefficients in a module over the base ring -/

section ModuleSide

variable {A : Type u} [CommRing A] {r : ℕ} (a : Fin r → A)

/-- The monomial `∏_i a_i^{e_i}` in the chosen elements of the base ring. -/
def moduleKoszulValue (e : Fin r → ℕ) : A := ∏ i, a i ^ e i

/-- The monomial with all exponents zero is `1`. -/
theorem moduleKoszulValue_zero : moduleKoszulValue a 0 = 1 := by
  simp [moduleKoszulValue]

/-- The monomial `∏_i a_i^{e_i}` is multiplicative in the exponent vector `e`. -/
theorem moduleKoszulValue_add (e e' : Fin r → ℕ) :
    moduleKoszulValue a (e + e') = moduleKoszulValue a e * moduleKoszulValue a e' := by
  rw [moduleKoszulValue, moduleKoszulValue, moduleKoszulValue, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => pow_add _ _ _

/-- **The system of copies of `N` underlying the Koszul complex with coefficients in an
`A`-module `N`**: the constant system `S ↦ N`, whose transition map along `S ⊆ T` is
multiplication by `∏_{i ∈ T ∖ S} a_i^{n+1}`. -/
def moduleKoszulPowerFunctor (N : ModuleCat.{u} A) (n : ℕ) :
    Finset (Fin r) ⥤ ModuleCat.{u} A where
  obj _ := N
  map {S T} g := moduleKoszulValue a (koszulExp n S T) • 𝟙 N
  map_id S := by rw [koszulExp_self, moduleKoszulValue_zero, one_smul]
  map_comp {S T V} g g' := by
    rw [koszulExp_add (leOfHom g) (leOfHom g'), moduleKoszulValue_add,
      Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul, mul_comm]

/-- **The Koszul complex on `a_1^{n+1}, …, a_r^{n+1}` with coefficients in `N`.** -/
def moduleKoszulPowerComplex (N : ModuleCat.{u} A) (n : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  AlternatingCech.complex (moduleKoszulPowerFunctor a N n)

/-- **The map of systems from the `(n+1)`-st to the `(n+2)`-nd Koszul powers** on the module
side: at the subset `S` it is multiplication by `a_S`. -/
def moduleKoszulPowerTrans (N : ModuleCat.{u} A) (n : ℕ) :
    moduleKoszulPowerFunctor a N n ⟶ moduleKoszulPowerFunctor a N (n + 1) where
  app S := moduleKoszulValue a (fun i => if i ∈ S then 1 else 0) • 𝟙 N
  naturality {S T} g := by
    change (moduleKoszulValue a (koszulExp n S T) • 𝟙 N) ≫ (moduleKoszulValue a _ • 𝟙 N) =
      (moduleKoszulValue a _ • 𝟙 N) ≫ (moduleKoszulValue a (koszulExp (n + 1) S T) • 𝟙 N)
    have he : (fun i => if i ∈ T then 1 else 0) + koszulExp n S T =
        koszulExp (n + 1) S T + (fun i : Fin r => if i ∈ S then 1 else 0) := by
      rw [add_comm, add_comm (koszulExp (n + 1) S T)]
      exact koszulExp_add_indicator (leOfHom g)
    simp only [Linear.comp_smul, Category.comp_id, smul_smul]
    rw [← moduleKoszulValue_add, ← moduleKoszulValue_add, he]

/-- The map of Koszul complexes with coefficients in `N`. -/
def moduleKoszulPowerComplexMap (N : ModuleCat.{u} A) (n : ℕ) :
    moduleKoszulPowerComplex a N n ⟶ moduleKoszulPowerComplex a N (n + 1) :=
  AlternatingCech.map (moduleKoszulPowerTrans a N n)

/-- **The tower of Koszul complexes on the positive powers of `a_1, …, a_r` with coefficients in
`N`.** -/
def moduleKoszulPowerSystem (N : ModuleCat.{u} A) : ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofSequence (moduleKoszulPowerComplexMap a N)

/-- The `n`-th term of `moduleKoszulPowerSystem` is `moduleKoszulPowerComplex a N n`. -/
@[simp]
theorem moduleKoszulPowerSystem_obj (N : ModuleCat.{u} A) (n : ℕ) :
    (moduleKoszulPowerSystem a N).obj n = moduleKoszulPowerComplex a N n :=
  rfl

end ModuleSide

/-! ## Global sections carry one Koszul tower to the other -/

section GlobalSections

/-- **`Hom(P, -)` preserves products of an arbitrary shape.** Forgetting the module structure
turns it into `CategoryTheory.coyoneda`, which preserves all limits; the forgetful functor of
`ModuleCat` reflects limits, so the preservation comes back. This is
`AlgebraicGeometry.RingedSite.preservesLimitsOfShape_preadditiveCoyonedaObj` of
`GlobalSectionsDerivedLimits.lean` at a shape other than `ℕ`, which is what the finite products
indexing the terms of a Koszul complex need. -/
theorem preservesLimitsOfShape_discrete_preadditiveCoyonedaObj
    {J : Type} {C : Type w} [Category.{v} C] [Preadditive C] [HasProductsOfShape J C] (P : C) :
    PreservesLimitsOfShape (Discrete J) (preadditiveCoyonedaObj P) := by
  have hpres : PreservesLimitsOfShape (Discrete J)
      (preadditiveCoyonedaObj P ⋙ forget (ModuleCat.{v} (End P)ᵐᵒᵖ)) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete J) (coyoneda.obj (op P)))
  have hrefl : ReflectsLimitsOfShape (Discrete J) (forget (ModuleCat.{v} (End P)ᵐᵒᵖ)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (preadditiveCoyonedaObj P) (forget _)

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- **`A`-linear global sections preserve products of an arbitrary shape.** -/
instance preservesLimitsOfShape_discrete_moduleGlobalSectionsOver_of_hasProductsOfShape
    (J : Type)
    [HasProductsOfShape J (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] :
    PreservesLimitsOfShape (Discrete J) (moduleGlobalSectionsOver X A ρ) := by
  have h₁ : PreservesLimitsOfShape (Discrete J)
      (preadditiveCoyonedaObj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    preservesLimitsOfShape_discrete_preadditiveCoyonedaObj _
  have h₂ : PreservesLimitsOfShape (Discrete J)
      (ModuleCat.restrictScalars.{u} ((globalSectionMulEnd X).comp ρ)) :=
    { preservesLimit := fun {_} ↦ inferInstance }
  exact Limits.comp_preservesLimitsOfShape
    (preadditiveCoyonedaObj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ModuleCat.restrictScalars ((globalSectionMulEnd X).comp ρ))

/-- **`A`-linear global sections preserve finite products**, which is what the comparison of
alternating Čech complexes of `CechBaseChange.lean` asks of a functor. -/
instance preservesFiniteProducts_moduleGlobalSectionsOver :
    PreservesFiniteProducts (moduleGlobalSectionsOver X A ρ) where
  preserves n :=
    preservesLimitsOfShape_discrete_moduleGlobalSectionsOver_of_hasProductsOfShape X A ρ (Fin n)

variable {r : ℕ} (a : Fin r → A)

/-- **The monomial in the global sections `ρ a_1, …, ρ a_r` of `𝒪` is the image under `ρ` of the
monomial in `a_1, …, a_r`.** `ρ` is a ring map into the compatible families of local sections and
evaluation at an object is a ring map out of them, so the composite carries a product of powers
to the product of the powers. -/
theorem koszulFamily_globalSectionOfSections (e : Fin r → ℕ) :
    koszulFamily X (fun i => globalSectionOfSections (ρ (a i))) e =
      ⟨(ρ (moduleKoszulValue a e)).1, fun g => (ρ (moduleKoszulValue a e)).2 g⟩ := by
  refine Subtype.ext (funext fun U => ?_)
  change koszulValue X (fun i => globalSectionOfSections (ρ (a i))) e U =
    (ρ (moduleKoszulValue a e)).1 U
  have hev : ∀ x : A, (ρ x).1 U = ((sectionsEval U).comp ρ) x := fun _ => rfl
  rw [koszulValue, hev, moduleKoszulValue, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, ← hev, globalSectionVal_globalSectionOfSections]
  rfl

/-- **`A`-linear global sections carry multiplication by the monomial in `ρ a_1, …, ρ a_r` to
multiplication by the monomial in `a_1, …, a_r`.** This is the one place the ring map `ρ` enters,
and it is `AlgebraicGeometry.RingedSite.map_globalSectionScalar_moduleGlobalSectionsOver` at the
monomial. -/
theorem map_koszulScalarOn (e : Fin r → ℕ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (moduleGlobalSectionsOver X A ρ).map
        (koszulScalarOn X (fun i => globalSectionOfSections (ρ (a i))) e M) =
      moduleKoszulValue a e • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj M) := by
  have h : koszulScalarOn X (fun i => globalSectionOfSections (ρ (a i))) e M =
      (globalSectionScalar X A ρ (moduleKoszulValue a e)).app M := by
    rw [koszulScalarOn, koszulFamily_globalSectionOfSections]
  rw [h]
  exact map_globalSectionScalar_moduleGlobalSectionsOver X A ρ _ M

/-- **Global sections carry the system of copies of `M` to the system of copies of
`Γ(𝒞, M)`.** Both systems are constant, so the comparison is the identity at each subset; its
naturality is `AlgebraicGeometry.RingedSite.map_koszulScalarOn`. -/
def globalSectionsKoszulPowerFunctorIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    koszulPowerFunctorOn X (fun i => globalSectionOfSections (ρ (a i))) M n ⋙
        moduleGlobalSectionsOver X A ρ ≅
      moduleKoszulPowerFunctor a ((moduleGlobalSectionsOver X A ρ).obj M) n :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {S T} _ =>
    Eq.trans (Category.comp_id _) (Eq.trans
      (map_koszulScalarOn X A ρ a (koszulExp n S T) M) (Category.id_comp _).symm)

/-- **`A`-linear global sections carry the Koszul complex with coefficients in `M` on the
`(n+1)`-st powers of `ρ a_1, …, ρ a_r` to the Koszul complex with coefficients in `Γ(𝒞, M)` on
the `(n+1)`-st powers of `a_1, …, a_r`.** This is the degreewise content of the projection
formula against the Koszul complexes, at an arbitrary number `r` of sections: the terms are
finite products, which `Γ(𝒞, -) = Hom_𝒪(𝒪, -)` preserves, and the entries of the differential
are multiplications by monomials, which it carries to the corresponding multiplications over
`A`. -/
def globalSectionsKoszulPowerComplexIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (koszulPowerComplexOn X (fun i => globalSectionOfSections (ρ (a i))) M n) ≅
      moduleKoszulPowerComplex a ((moduleGlobalSectionsOver X A ρ).obj M) n :=
  AlternatingCech.mapComplexIso (moduleGlobalSectionsOver X A ρ)
      (koszulPowerFunctorOn X (fun i => globalSectionOfSections (ρ (a i))) M n) ≪≫
    AlternatingCech.mapIso (globalSectionsKoszulPowerFunctorIso X A ρ a M n)

/-- The forward map of `globalSectionsKoszulPowerComplexIso` is the composite of the comparison
isomorphism for `AlternatingCech.complex` with the map induced by
`globalSectionsKoszulPowerFunctorIso`. -/
theorem globalSectionsKoszulPowerComplexIso_hom
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    (globalSectionsKoszulPowerComplexIso X A ρ a M n).hom =
      (AlternatingCech.mapComplexIso (moduleGlobalSectionsOver X A ρ)
          (koszulPowerFunctorOn X (fun i => globalSectionOfSections (ρ (a i))) M n)).hom ≫
        AlternatingCech.map (globalSectionsKoszulPowerFunctorIso X A ρ a M n).hom :=
  rfl

/-- The comparison is compatible with the transition maps of the two towers: on either side the
transition map at the subset `S` is multiplication by the monomial indexed by `S`. -/
theorem globalSectionsKoszulPowerFunctorIso_trans
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    Functor.whiskerRight (koszulPowerTransOn X (fun i => globalSectionOfSections (ρ (a i))) M n)
          (moduleGlobalSectionsOver X A ρ) ≫
        (globalSectionsKoszulPowerFunctorIso X A ρ a M (n + 1)).hom =
      (globalSectionsKoszulPowerFunctorIso X A ρ a M n).hom ≫
        moduleKoszulPowerTrans a ((moduleGlobalSectionsOver X A ρ).obj M) n := by
  refine NatTrans.ext (funext fun S => ?_)
  exact Eq.trans (Category.comp_id _) (Eq.trans
    (map_koszulScalarOn X A ρ a (fun i => if i ∈ S then 1 else 0) M) (Category.id_comp _).symm)

/-- **`A`-linear global sections carry one Koszul tower to the other**, compatibly with the
transition maps. -/
def globalSectionsKoszulPowerSystemMap
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    koszulPowerSystemOn X (fun i => globalSectionOfSections (ρ (a i))) M ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      moduleKoszulPowerSystem a ((moduleGlobalSectionsOver X A ρ).obj M) :=
  NatTrans.ofSequence
    (fun n => (globalSectionsKoszulPowerComplexIso X A ρ a M n).hom) fun n => by
    change ((moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((koszulPowerSystemOn X (fun i => globalSectionOfSections (ρ (a i))) M).map
          (homOfLE n.le_succ)) ≫
        (globalSectionsKoszulPowerComplexIso X A ρ a M (n + 1)).hom =
      (globalSectionsKoszulPowerComplexIso X A ρ a M n).hom ≫
        (moduleKoszulPowerSystem a ((moduleGlobalSectionsOver X A ρ).obj M)).map
          (homOfLE n.le_succ)
    rw [show (koszulPowerSystemOn X (fun i => globalSectionOfSections (ρ (a i))) M).map
            (homOfLE n.le_succ) =
          koszulPowerComplexOnMap X (fun i => globalSectionOfSections (ρ (a i))) M n from
        Functor.ofSequence_map_homOfLE_succ _ n,
      show (moduleKoszulPowerSystem a ((moduleGlobalSectionsOver X A ρ).obj M)).map
            (homOfLE n.le_succ) =
          moduleKoszulPowerComplexMap a ((moduleGlobalSectionsOver X A ρ).obj M) n from
        Functor.ofSequence_map_homOfLE_succ _ n]
    exact AlternatingCech.mapComplexIso_trans_mapIso_map (moduleGlobalSectionsOver X A ρ)
      (koszulPowerTransOn X (fun i => globalSectionOfSections (ρ (a i))) M n)
      (globalSectionsKoszulPowerFunctorIso X A ρ a M n)
      (globalSectionsKoszulPowerFunctorIso X A ρ a M (n + 1))
      (moduleKoszulPowerTrans a ((moduleGlobalSectionsOver X A ρ).obj M) n)
      (globalSectionsKoszulPowerFunctorIso_trans X A ρ a M n)

/-- The comparison `globalSectionsKoszulPowerSystemMap` of Koszul towers is an isomorphism. -/
instance isIso_globalSectionsKoszulPowerSystemMap
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso (globalSectionsKoszulPowerSystemMap X A ρ a M) := by
  have hi (n : ℕ) : IsIso ((globalSectionsKoszulPowerSystemMap X A ρ a M).app n) := by
    change IsIso (globalSectionsKoszulPowerComplexIso X A ρ a M n).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **`A`-linear global sections carry one Koszul tower to the other**, as an isomorphism of
inverse systems of complexes of `A`-modules. -/
def globalSectionsKoszulPowerSystemIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    koszulPowerSystemOn X (fun i => globalSectionOfSections (ρ (a i))) M ⋙
        (moduleGlobalSectionsOver X A ρ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      moduleKoszulPowerSystem a ((moduleGlobalSectionsOver X A ρ).obj M) :=
  asIso (globalSectionsKoszulPowerSystemMap X A ρ a M)

end GlobalSections

end AlgebraicGeometry.RingedSite

end

