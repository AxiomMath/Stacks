module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The Koszul complexes of a finite family of global sections on a ringed site

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. For `n ≥ 1` the
Koszul complex `K(𝒪, f_1^n, …, f_r^n)` is a bounded complex of finite free `𝒪`-modules, and
[Stacks, Tag 0A0E] computes the derived completion of `K ∈ D(𝒪)` along the ideal sheaf generated
by `f_1, …, f_r` as the derived limit of the tower `n ↦ K ⊗^𝐋_𝒪 K_n`, where `K_n` is the
`𝒪`-dual of that complex. This file constructs the Koszul complexes themselves, together with
the maps relating successive powers, as a sequential diagram of cochain complexes of sheaves of
`𝒪`-modules.

The construction is the one of [Stacks, Tag 0913]: in the grading in which it is compared with
the extended alternating Čech complex, the Koszul complex on `f_1^n, …, f_r^n` has
`∏_{|S| = p} 𝒪` in degree `p`, the factors being indexed by the subsets `S ⊆ {1, …, r}` of
cardinality `p`, and its differential is the alternating sum of the maps `𝒪 ⟶ 𝒪` given by
multiplication by `f_{T ∖ S}^n` for `S ⊆ T` with `|T| = |S| + 1`. That is the *same* shape as the
extended alternating Čech complex, whose degree-`p` term is `∏_{|S| = p} 𝒪_{f_S}` and whose
differential is assembled from the localization maps `𝒪_{f_S} ⟶ 𝒪_{f_T}`: both are
`CategoryTheory.AlternatingCech.complex` applied to a functor on the poset of subsets of
`Fin r`, the Koszul complex to the constant functor `S ↦ 𝒪` with multiplication by
`f_{T ∖ S}^n` as transition maps, and the Čech complex to
`AlgebraicGeometry.RingedSite.awayLocalizationFunctor`.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulScalar`: multiplication by a monomial `∏ f_i^{e_i}` in the
  chosen global sections, as an endomorphism of `𝒪` read as a sheaf of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.koszulPowerFunctor`: the system `S ↦ 𝒪` on the poset of subsets
  of `Fin r` whose transition map along `S ⊆ T` is multiplication by `f_{T ∖ S}^{n + 1}`.
* `AlgebraicGeometry.RingedSite.koszulPowerComplex`: the Koszul complex
  `K(𝒪, f_1^{n+1}, …, f_r^{n+1})`, in degrees `0, …, r`.
* `AlgebraicGeometry.RingedSite.koszulPowerSystem`: the sequential diagram
  `ℕ ⥤ CochainComplex (Mod 𝒪) ℤ` of those complexes and the maps between successive powers.
* `CategoryTheory.AlternatingCech.map`: the map of alternating Čech complexes induced by a
  morphism of systems indexed by the subsets of `Fin r`.
* `CategoryTheory.AlternatingCech.mapIso`: the isomorphism of alternating Čech complexes induced
  by an isomorphism of systems.

## Main results

* `CategoryTheory.AlternatingCech.d_comp_map`: the induced map commutes with the alternating
  differential.
* `CategoryTheory.AlternatingCech.map_id` and `CategoryTheory.AlternatingCech.map_comp`:
  `map` is functorial.
* `AlgebraicGeometry.RingedSite.koszulScalar_comp`: multiplication by monomials composes by
  adding exponents.
* `AlgebraicGeometry.RingedSite.isZero_koszulPowerComplex_X_of_neg` and
  `AlgebraicGeometry.RingedSite.isZero_koszulPowerComplex_X_of_lt`: the Koszul complex is
  concentrated in degrees `0, …, r`.

## Implementation notes

The index `n` stands for the exponent `n + 1`, as in [Stacks, Tag 0A0E], where the tower is
indexed by the *positive* powers; the powers `n + 1` for `n : ℕ` are cofinal among them.

Multiplication by a monomial is `Stacks.SheafOfModules.globalSectionToEnd` — multiplication by
a compatible family of local sections, as an endomorphism of the identity functor of `Mod(𝒪)` —
evaluated at `SheafOfModules.unit`. The compatible family is the monomial
`U ↦ ∏_i (f_i|_U)^{e_i}`, whose compatibility with restriction is `map_prod` and `map_pow` for
the restriction maps together with
`AlgebraicGeometry.RingedSite.globalSectionVal_map`. Exponent vectors `e : Fin r → ℕ` rather
than subsets are used because then every identity needed below is the single lemma
`koszulScalar_comp`, that composing multiplications adds exponents, followed by a pointwise
comparison of exponent vectors; a formulation by subsets would need the disjointness of
`T ∖ S` and `V ∖ T` as a separate input at each use.

The terms of the Koszul complex are *categorical products* of copies of `𝒪` over the finite
index type `AlternatingCech.Idx r p`, not exterior powers of a finite free module: in this
grading the Koszul complex has no exterior algebra in it, so none of the sheaf-condition
machinery for exterior powers — which the library has only for a ringed *space*,
`PresheafOfModules.isSheaf_exteriorAlgebraPiece_finFree` of
`StacksFrontier/AlgebraicGeometry/Koszul/Sheaf/SheafCondition.lean` — is needed, and the complex
exists over an arbitrary ringed site.

The formula of [Stacks, Tag 0A0E] for these complexes is
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDualSystem_koszulPowerSystem_canonical`
of `KoszulCechHomotopyColimit.lean`, in the spelling `K ⊗^𝐋_𝒪 K_n^∨` of [Stacks, Tag 0A0A] with
`K_n` the complex in degrees `0, …, r` built here, and
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorKoszulComplex_completionFunctor` of
`KoszulCompletionFormula.lean`, with the dual complex in degrees `-r, …, 0`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.AlternatingCech

variable {r : ℕ} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]
  {F G : Finset (Fin r) ⥤ 𝒜}

/-- The degreewise map of alternating Čech complexes induced by a morphism of systems: in degree
`p` it is the product over the subsets of cardinality `p` of the components of the morphism. -/
def mapX (α : F ⟶ G) (p : ℤ) : term F p ⟶ term G p :=
  Limits.Pi.map fun S : Idx r p => α.app S.1

omit [Preadditive 𝒜] in
/-- The component at a subset `A` of the degreewise map induced by `α` is the component of `α` at
`A`. -/
@[simp]
theorem mapX_comp_pi (α : F ⟶ G) {p : ℤ} (A : Idx r p) :
    mapX α p ≫ Pi.π (fun S : Idx r p => G.obj S.1) A =
      Pi.π (fun S : Idx r p => F.obj S.1) A ≫ α.app A.1 :=
  Limits.Pi.map_π _ _

omit [Preadditive 𝒜] in
/-- The degreewise map induced by `α` commutes with the projection to the factor indexed by `A`
followed by the transition map along `A ⊆ W`. -/
theorem mapX_comp_proj (α : F ⟶ G) {p : ℤ} (A : Idx r p) {W : Finset (Fin r)} (h : A.1 ⊆ W) :
    mapX α p ≫ proj G A h = proj F A h ≫ α.app W := by
  rw [proj, proj, ← Category.assoc, mapX_comp_pi, Category.assoc, Category.assoc, α.naturality]

/-- **The induced degreewise map commutes with the alternating differential.** -/
theorem d_comp_map (α : F ⟶ G) (p : ℤ) :
    d F p ≫ mapX α (p + 1) = mapX α p ≫ d G p := by
  refine Pi.hom_ext _ _ fun T => ?_
  rw [Category.assoc, mapX_comp_pi, ← Category.assoc, d_comp_pi, Category.assoc, d_comp_pi,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, mapX_comp_proj]

/-- **The map of alternating Čech complexes induced by a morphism of systems** indexed by the
subsets of `Fin r`. -/
def map (α : F ⟶ G) : complex F ⟶ complex G where
  f p := mapX α p
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [complex_d, complex_d]
    exact (d_comp_map α p).symm

/-- In degree `p`, the map of complexes induced by `α` is `mapX α p`. -/
@[simp]
theorem map_f (α : F ⟶ G) (p : ℤ) : (map α).f p = mapX α p := rfl

omit [Preadditive 𝒜] in
/-- The degreewise map induced by the identity of a system is the identity. -/
theorem mapX_id (p : ℤ) : mapX (𝟙 F) p = 𝟙 (term F p) := by
  refine Pi.hom_ext _ _ fun A => ?_
  rw [mapX_comp_pi]
  simp

/-- **The map of complexes induced by the identity of a system is the identity.** -/
@[simp]
theorem map_id : map (𝟙 F) = 𝟙 (complex F) := by
  ext p
  rw [map_f, mapX_id]
  rfl

omit [Preadditive 𝒜] in
/-- The degreewise maps of alternating Čech complexes induced by two morphisms of systems
compose. -/
theorem mapX_comp_mapX {H : Finset (Fin r) ⥤ 𝒜} (α : F ⟶ G) (β : G ⟶ H) (p : ℤ) :
    mapX α p ≫ mapX β p = mapX (α ≫ β) p := by
  refine Limits.Pi.hom_ext _ _ fun A => ?_
  rw [Category.assoc, mapX_comp_pi, ← Category.assoc, mapX_comp_pi, Category.assoc,
    mapX_comp_pi, NatTrans.comp_app]

/-- **The maps of complexes induced by a composite of morphisms of systems compose.** -/
theorem map_comp {H : Finset (Fin r) ⥤ 𝒜} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ≫ map β :=
  HomologicalComplex.hom_ext _ _ fun p => (mapX_comp_mapX α β p).symm

/-- **An isomorphism of systems indexed by the subsets of `Fin r` induces an isomorphism of their
extended alternating Čech complexes.** -/
@[simps]
def mapIso (e : F ≅ G) : complex F ≅ complex G where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

open scoped IsMulCommutative

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The value over an object of the site of the monomial `∏_i f_i^{e_i}` in the chosen global
sections. -/
def koszulValue (e : Fin r → ℕ) (U : X.Cᵒᵖ) : X.O.obj.obj U :=
  ∏ i, globalSectionVal (f i) U ^ e i

/-- The empty monomial is the unit section. -/
theorem koszulValue_zero (U : X.Cᵒᵖ) : koszulValue X f 0 U = 1 := by
  simp [koszulValue]

/-- Monomials multiply by adding exponents. -/
theorem koszulValue_add (e e' : Fin r → ℕ) (U : X.Cᵒᵖ) :
    koszulValue X f (e + e') U = koszulValue X f e U * koszulValue X f e' U := by
  rw [koszulValue, koszulValue, koszulValue, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => pow_add _ _ _

/-- Monomials commute, and their product is the monomial with the exponents added. -/
theorem koszulValue_mul_comm (e e' : Fin r → ℕ) (U : X.Cᵒᵖ) :
    koszulValue X f e' U * koszulValue X f e U = koszulValue X f (e + e') U := by
  rw [koszulValue_add, mul_comm]

/-- Restriction carries a monomial in the chosen global sections to the monomial with the same
exponents. -/
theorem koszulValue_map (e : Fin r → ℕ) {U V : X.Cᵒᵖ} (g : U ⟶ V) :
    (X.O.obj.map g).hom (koszulValue X f e U) = koszulValue X f e V := by
  rw [koszulValue, koszulValue, map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [map_pow, globalSectionVal_map (f i) g]

/-- The monomial `∏_i f_i^{e_i}`, as a compatible family of local sections of the structure
sheaf. -/
def koszulFamily (e : Fin r → ℕ) :
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⋙ forget RingCat.{u}).sections where
  val U := koszulValue X f e U
  property {_U _V} g := koszulValue_map X f e g

/-- The monomial `∏_i f_i^{e_i}` read as a section of the sheaf of rings
`AlgebraicGeometry.RingedSite.ringSheaf`, which is the structure sheaf with its commutativity
forgotten. -/
def koszulRingValue (e : Fin r → ℕ) (U : X.Cᵒᵖ) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U :=
  koszulValue X f e U

/-- **Multiplication by the monomial `∏_i f_i^{e_i}`**, as an endomorphism of `𝒪` read as a
sheaf of `𝒪`-modules. -/
def koszulScalar (e : Fin r → ℕ) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (koszulFamily X f e)).app
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- On local sections over `U`, `koszulScalar` is multiplication by the monomial
`∏_i f_i^{e_i}` over `U`. -/
theorem koszulScalar_app (e : Fin r → ℕ) (U : X.Cᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj U) :
    (koszulScalar X f e).val.app U x = koszulRingValue X f e U • x :=
  rfl

/-- **Composing multiplications adds exponents.** -/
theorem koszulScalar_comp (e e' : Fin r → ℕ) :
    koszulScalar X f e ≫ koszulScalar X f e' = koszulScalar X f (e + e') := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show koszulRingValue X f e' U • (koszulRingValue X f e U • x) =
    koszulRingValue X f (e + e') U • x
  rw [← mul_smul]
  exact congrArg (fun c : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U => c • x)
    (koszulValue_mul_comm X f e e' U)

/-- Multiplication by the empty monomial is the identity. -/
theorem koszulScalar_zero :
    koszulScalar X f 0 =
      𝟙 (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show koszulRingValue X f 0 U • x = x
  rw [show koszulRingValue X f 0 U = 1 from koszulValue_zero X f U]
  exact one_smul _ x

/-- Multiplication depends on the exponent vector only through its values. -/
theorem koszulScalar_congr {e e' : Fin r → ℕ} (h : ∀ i, e i = e' i) :
    koszulScalar X f e = koszulScalar X f e' := by
  rw [funext h]

/-- The exponent vector of the transition map of the Koszul complex on the `(n+1)`-st powers
along an inclusion `S ⊆ T`: the exponent `n + 1` at the indices of `T ∖ S`. -/
def koszulExp (n : ℕ) (S T : Finset (Fin r)) : Fin r → ℕ :=
  fun i => if i ∈ T \ S then n + 1 else 0

/-- **The system of free rank-one modules underlying the Koszul complex on the `(n+1)`-st powers
of the chosen global sections**: the constant system `S ↦ 𝒪` on the poset of subsets of
`Fin r`, whose transition map along `S ⊆ T` is multiplication by `f_{T ∖ S}^{n+1}`. -/
def koszulPowerFunctor (n : ℕ) :
    Finset (Fin r) ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  obj _ := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  map {S T} g := koszulScalar X f (koszulExp n S T)
  map_id S := by
    rw [show koszulExp n S S = 0 from funext fun i => by simp [koszulExp]]
    exact koszulScalar_zero X f
  map_comp {S T V} g g' := by
    rw [koszulScalar_comp]
    refine koszulScalar_congr X f fun i => ?_
    have hST : S ⊆ T := leOfHom g
    have hTV : T ⊆ V := leOfHom g'
    by_cases hiT : i ∈ T
    · by_cases hiS : i ∈ S <;>
        simp [koszulExp, hiT, hiS, hTV hiT, Finset.mem_sdiff]
    · by_cases hiV : i ∈ V <;>
        simp [koszulExp, hiT, hiV, Finset.mem_sdiff,
          show i ∉ S from fun hiS => hiT (hST hiS)]

/-- **The Koszul complex `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` of sheaves of `𝒪`-modules**, in the
grading of [Stacks, Tag 0913] in which it is compared with the extended alternating Čech
complex: the term in degree `p` is the product of copies of `𝒪` indexed by the subsets of
`{1, …, r}` of cardinality `p`, and the differential is the alternating sum of the
multiplications by `f_{T ∖ S}^{n+1}`. It is concentrated in degrees `0, …, r`. -/
def koszulPowerComplex (n : ℕ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  AlternatingCech.complex (koszulPowerFunctor X f n)

/-- Every term of the system `koszulPowerFunctor` is the structure sheaf `𝒪`. -/
@[simp]
theorem koszulPowerFunctor_obj (n : ℕ) (S : Finset (Fin r)) :
    (koszulPowerFunctor X f n).obj S =
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  rfl

/-- The term in degree `p` of the Koszul complex is the degree-`p` term of the alternating Čech
complex of `koszulPowerFunctor`. -/
@[simp]
theorem koszulPowerComplex_X (n : ℕ) (p : ℤ) :
    (koszulPowerComplex X f n).X p = AlternatingCech.term (koszulPowerFunctor X f n) p :=
  rfl

/-- The Koszul complex vanishes in a degree with no subsets of that cardinality. -/
private theorem isZero_koszulPowerComplex_X_of_isEmpty (n : ℕ) {p : ℤ}
    (h : IsEmpty (AlternatingCech.Idx r p)) : IsZero ((koszulPowerComplex X f n).X p) :=
  (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun b => h.elim b)

/-- The Koszul complex vanishes in negative degrees. -/
theorem isZero_koszulPowerComplex_X_of_neg (n : ℕ) {p : ℤ} (hp : p < 0) :
    IsZero ((koszulPowerComplex X f n).X p) :=
  isZero_koszulPowerComplex_X_of_isEmpty X f n (AlternatingCech.isEmpty_idx_of_neg hp)

/-- The Koszul complex vanishes above degree `r`. -/
theorem isZero_koszulPowerComplex_X_of_lt (n : ℕ) {p : ℤ} (hp : (r : ℤ) < p) :
    IsZero ((koszulPowerComplex X f n).X p) :=
  isZero_koszulPowerComplex_X_of_isEmpty X f n (AlternatingCech.isEmpty_idx_of_lt hp)

/-- **The map of systems from the `(n+1)`-st to the `(n+2)`-nd Koszul powers**: at the subset
`S` it is multiplication by `f_S`. -/
def koszulPowerTrans (n : ℕ) : koszulPowerFunctor X f n ⟶ koszulPowerFunctor X f (n + 1) where
  app S := koszulScalar X f (fun i => if i ∈ S then 1 else 0)
  naturality {S T} g := by
    change koszulScalar X f (koszulExp n S T) ≫ koszulScalar X f _ =
      koszulScalar X f _ ≫ koszulScalar X f (koszulExp (n + 1) S T)
    rw [koszulScalar_comp, koszulScalar_comp]
    refine koszulScalar_congr X f fun i => ?_
    have hST : S ⊆ T := leOfHom g
    by_cases hiT : i ∈ T
    · by_cases hiS : i ∈ S <;> simp [koszulExp, hiT, hiS, Finset.mem_sdiff]
    · simp [koszulExp, hiT, Finset.mem_sdiff, show i ∉ S from fun hiS => hiT (hST hiS)]

/-- The map `K(𝒪, f^{n+1}) ⟶ K(𝒪, f^{n+2})` of Koszul complexes, multiplication by `f_S` in the
factor indexed by `S`. -/
def koszulPowerComplexMap (n : ℕ) :
    koszulPowerComplex X f n ⟶ koszulPowerComplex X f (n + 1) :=
  AlternatingCech.map (koszulPowerTrans X f n)

/-- **The sequential diagram of the Koszul complexes on the positive powers of
`f_1, …, f_r`**, with the maps `koszulPowerComplexMap` between successive powers. The index `n`
carries the exponent `n + 1`. -/
def koszulPowerSystem :
    ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  Functor.ofSequence (koszulPowerComplexMap X f)

/-- The `n`-th object of `koszulPowerSystem` is the Koszul complex on the `(n+1)`-st powers. -/
@[simp]
theorem koszulPowerSystem_obj (n : ℕ) :
    (koszulPowerSystem X f).obj n = koszulPowerComplex X f n :=
  rfl

end AlgebraicGeometry.RingedSite

end
