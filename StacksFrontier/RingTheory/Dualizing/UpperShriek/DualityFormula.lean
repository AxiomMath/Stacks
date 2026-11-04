module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormula
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Surjective

/-!
# Algebraic upper shriek as the dual of the base change of the dual

Let `φ : A →+* B` be a homomorphism of Noetherian rings of finite type, let `ω_A` be a dualizing
complex for `A`, put `ω_B = φ^!(ω_A)`, and write `D_A(K) = RHom_A(K, ω_A)` and
`D_B(L) = RHom_B(L, ω_B)`.  Then

`φ^!(K) = D_B(D_A(K) ⊗_A^L B)`

for `K` in `D_Coh(A)`, *functorially in `K`*.  This is [Stacks, Tag 0E9L].  The case proved here
is the one the source disposes of by adjunction and Yoneda, namely `φ` surjective, where `φ^!`
is derived coextension of scalars `RHom_A(B, -)`; and it is proved functorially, as an
isomorphism of functors on `D_Coh(A)`.  The general finite-type case is
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FiniteTypeDualityFormula`.

## Main results

* `Dualizing.derivedHomIsoDualizingDerivedHom` — the formula with
  `φ^!` replaced by derived coextension of scalars `RHom_A(B, -)`, for an arbitrary ring
  homomorphism, at each `K` of `D_Coh(A)`.
* `Dualizing.derivedHomNatIsoDualizingDerivedHom` — the same, as an isomorphism of functors on
  `D_Coh(A)`.
* `Dualizing.upperShriekFunctor_ofSurjective_natIso_dualizingDerivedHom` — **[Stacks, Tag 0E9L]
  for a surjective `φ`**, at its presentation with no variables, as an isomorphism of functors
  on `D_Coh(A)`.
* `Dualizing.upperShriekFunctor_ofSurjective_iso_dualizingDerivedHom` — its value at a single
  `K`.

## Implementation notes

### The proof

The source's argument for a surjection is a chain of five natural identifications of
`Hom_B(F, -)` groups followed by Yoneda, and that is what is carried out below.  Writing
`i_*` for restriction of scalars from `D(B)` to `D(A)`, `N = D_A(K)` and `M = N ⊗_A^L B`:

* `Hom_B(F, D_B(M)) = Hom_B(F ⊗_B^L M, ω_B)` by the derived tensor--Hom adjunction over `B`,
  which is [Stacks, Tag 0A63] — here the `homEquiv` field of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`;
* `Hom_B(F ⊗_B^L M, ω_B) = Hom_A(i_*(F ⊗_B^L M), ω_A)` because `ω_B = RHom_A(B, ω_A)` and
  derived coextension of scalars is right adjoint to `i_*`, which is [Stacks, Tag 0A70];
* `Hom_A(i_*(F ⊗_B^L M), ω_A) = Hom_A(i_*F ⊗_A^L N, ω_A)` by the projection formula
  `i_*(F ⊗_B^L (N ⊗_A^L B)) = i_*F ⊗_A^L N`;
* `Hom_A(i_*F ⊗_A^L N, ω_A) = Hom_A(i_*F, D_A(N)) = Hom_A(i_*F, K)` by the derived tensor--Hom
  adjunction over `A` and biduality `D_A(D_A(K)) = K`, which is [Stacks, Tag 0A7C] in the form
  `Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`;
* `Hom_A(i_*F, K) = Hom_B(F, RHom_A(B, K))` by [Stacks, Tag 0A70] again.

The chain is packaged as the bijection `Dualizing.dualityFormulaHomEquiv`, and the two Yoneda
arguments are its two naturality statements: `dualityFormulaHomEquiv_naturality_source` in the
test object `F`, which gives the isomorphism at a fixed `K`, and
`dualityFormulaHomEquiv_naturality_target` in `K`, which makes the resulting family an
isomorphism of functors.  `Dualizing.natIsoOfHomEquiv` is the Yoneda argument in that
two-variable form: a family of Hom-bijections natural in both variables is the Hom-bijection of
an isomorphism of functors.

Biduality is discharged, not assumed: over a Noetherian ring, the canonical morphism
`K ⟶ RHom_A(RHom_A(K, ω_A), ω_A)` is invertible for every `K` with finite cohomology in every
degree, and `D_Coh(A)` is exactly that condition.  So `K ∈ D_Coh(A)` enters as the finiteness
hypothesis `hK`, which is the hypothesis of the tag; the functorial statement is made on the
full subcategory `Dualizing.hasFiniteCohomology A` cut out by it.  Naturality of biduality in
`K`, which the functorial statement needs, is `Dualizing.bidualityMor_naturality`.

### Where the projection formula comes from

The projection formula `i_*(F ⊗_B^L (N ⊗_A^L B)) ≅ i_*F ⊗_A^L N` is
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso`, an isomorphism of bifunctors: natural
in `F` *and* in `N`.  The intermediate `Dualizing.derivedHomIsoDualizingDerivedHom` and
`Dualizing.derivedHomNatIsoDualizingDerivedHom` take it as the arguments `hproj`, `hprojNat` and
`hprojNatN`, since that keeps the steps of the argument they perform separate from the
construction of the formula; the tagged theorem builds all three from
`derivedProjBifunctorNatIso` and passes them in, so nothing is left open.  `hprojNat` is
naturality in `F` and `hprojNatN` naturality in `N`; the latter is exactly what functoriality in
`K` of the five-step chain reduces to, since the third step is the projection formula read at
`N = D_A(K)` and a map `K ⟶ K'` moves it to `N' = D_A(K')`.

The formula is proved for an arbitrary ring homomorphism from the chain-level projection formula
of [Stacks, Tag 06Y6] — the comparison
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`, natural in the complex of
`B`-modules and in the complex of `A`-modules alike — and descended along the localization
functor in the `B`-variable and along the K-flat resolving class in the `A`-variable, with no
resolution chosen object by object.

`i_*` is an arbitrary left adjoint of `RHom_A(B, -)`, not a particular model of derived
restriction of scalars.  By uniqueness of adjoints that is the same functor up to isomorphism,
and [Stacks, Tag 0A70] — `Dualizing.restrictScalarsDerived_adj_derivedHom` — provides such an
adjunction; stating it this way is stronger and avoids depending on how the exactness instances
of restriction of scalars happen to be found.

Derived base change `- ⊗_A^L B` is likewise an arbitrary normalized model, taken as a
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`, so no choice is made.

## References

* [Stacks Project, Tag 0E9L](https://stacks.math.columbia.edu/tag/0E9L)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

open StacksDraft.DerivedHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Transposing a morphism out of a derived tensor product precomposed in the first variable:
the inverse form of the left naturality of the Hom equivalence of [Stacks, Tag 0A63]. -/
theorem homEquiv_symm_tensor_map_comp
    (d : DerivedHomAdjunction A) {X X' L M : DerivedCategory (ModuleCat.{max u v} A)}
    (g : X' ⟶ X) (c : d.tensor.obj (X, L) ⟶ M) :
    (d.homEquiv X' L M).symm
        (d.tensor.map (X := (X', L)) (Y := (X, L)) (g, 𝟙 L) ≫ c) =
      g ≫ (d.homEquiv X L M).symm c := by
  apply (d.homEquiv X' L M).injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_naturality_left, AddEquiv.apply_symm_apply]

/-- **Yoneda for a functor.** A family of bijections `(Z ⟶ S K) ≃ (Z ⟶ T K)` natural in the
test object `Z` and in `K` is the Hom-bijection of an isomorphism of functors `S ≅ T`.  This is
the two-variable form of `CategoryTheory.Yoneda.ext`: naturality in `Z` makes each component an
isomorphism, naturality in `K` makes the components natural. -/
def natIsoOfHomEquiv {J : Type*} [Category J] {D : Type*} [Category D] (S T : J ⥤ D)
    (e : ∀ (K : J) (Z : D), (Z ⟶ S.obj K) ≃ (Z ⟶ T.obj K))
    (hZ : ∀ (K : J) {Z Z' : D} (g : Z' ⟶ Z) (a : Z ⟶ S.obj K),
      e K Z' (g ≫ a) = g ≫ e K Z a)
    (hK : ∀ {K K' : J} (f : K ⟶ K') (Z : D) (a : Z ⟶ S.obj K),
      e K' Z (a ≫ S.map f) = e K Z a ≫ T.map f) :
    S ≅ T :=
  have hn : ∀ (K : J) {Z Z' : D} (g : Z' ⟶ Z) (b : Z ⟶ T.obj K),
      (e K Z').symm (g ≫ b) = g ≫ (e K Z).symm b := by
    intro K Z Z' g b
    apply (e K Z').injective
    rw [Equiv.apply_symm_apply, hZ K g ((e K Z).symm b), Equiv.apply_symm_apply]
  NatIso.ofComponents (fun K =>
    { hom := e K (S.obj K) (𝟙 _)
      inv := (e K (T.obj K)).symm (𝟙 _)
      hom_inv_id := by
        have hg := hn K (e K (S.obj K) (𝟙 (S.obj K))) (𝟙 (T.obj K))
        rw [Category.comp_id] at hg
        rw [← hg, Equiv.symm_apply_apply]
      inv_hom_id := by
        have hg := hZ K ((e K (T.obj K)).symm (𝟙 (T.obj K))) (𝟙 (S.obj K))
        rw [Category.comp_id] at hg
        rw [← hg, Equiv.apply_symm_apply] })
    (by
      intro K K' f
      have h1 := hZ K' (S.map f) (𝟙 (S.obj K'))
      have h2 := hK f (S.obj K) (𝟙 (S.obj K))
      rw [Category.comp_id] at h1
      rw [Category.id_comp] at h2
      dsimp only
      rw [← h1, ← h2])

/-- Transposing a morphism out of a derived tensor product precomposed in the tensor factor. -/
theorem homEquiv_symm_tensor_map_comp_middle
    (d : DerivedHomAdjunction A) {X L L' M : DerivedCategory (ModuleCat.{max u v} A)}
    (g : L' ⟶ L) (c : d.tensor.obj (X, L) ⟶ M) :
    (d.homEquiv X L' M).symm
        (d.tensor.map (X := (X, L')) (Y := (X, L)) (𝟙 X, g) ≫ c) =
      (d.homEquiv X L M).symm c ≫
        d.hom.map ((g.op, 𝟙 M) : (Opposite.op L, M) ⟶ (Opposite.op L', M)) := by
  apply (d.homEquiv X L' M).injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_dinaturality, AddEquiv.apply_symm_apply]

/-- `D_Coh(A)`: the objects of `D(A)` whose cohomology modules are all finite. -/
def hasFiniteCohomology (A : Type u) [CommRing A] :
    ObjectProperty (DerivedCategory (ModuleCat.{max u v} A)) :=
  fun K => ∀ i : ℤ, Module.Finite A
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)

/-- The functor `K ↦ D_B(D_A(K) ⊗_A^L B)` of [Stacks, Tag 0E9L]. -/
def dualizingBaseChangeFunctor (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (ωA : DerivedCategory (ModuleCat.{max u v} A))
    (ωB : DerivedCategory (ModuleCat.{max u v} B)) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤ DerivedCategory (ModuleCat.{max u v} B) :=
  (dualizingDerivedHomFunctor.{u, v} A ωA ⋙ E.functor).rightOp ⋙
    dualizingDerivedHomFunctor.{u, v} B ωB

/-- Changing the dualizing object along an isomorphism. -/
def dualizingDerivedHomFunctorIsoOfIso (B : Type u) [CommRing B]
    {ω ω' : DerivedCategory (ModuleCat.{max u v} B)} (eω : ω ≅ ω') :
    dualizingDerivedHomFunctor.{u, v} B ω ≅ dualizingDerivedHomFunctor.{u, v} B ω' :=
  NatIso.ofComponents
    (fun X => (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.mapIso
      (Iso.prod (Iso.refl X) eω))
    (by
      intro X Y h
      change (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map _ ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map _ =
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map _ ≫
            (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      refine congrArg (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map
        (Prod.ext ?_ ?_)
      · simp
      · simp)

/-- Changing the dualizing object of the target in `Dualizing.dualizingBaseChangeFunctor`. -/
def dualizingBaseChangeFunctorIsoOfIso (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (ωA : DerivedCategory (ModuleCat.{max u v} A))
    {ωB ωB' : DerivedCategory (ModuleCat.{max u v} B)} (eω : ωB ≅ ωB') :
    dualizingBaseChangeFunctor.{u, v} φ E ωA ωB ≅
      dualizingBaseChangeFunctor.{u, v} φ E ωA ωB' :=
  Functor.isoWhiskerLeft _ (dualizingDerivedHomFunctorIsoOfIso.{u, v} B eω)

/-- The biduality isomorphism of [Stacks, Tag 0A7C] at an object of `D_Coh(A)`. -/
def dualizingBidualityIso [IsNoetherianRing A]
    (ωA K : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    K ≅ (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
      (Opposite.op ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
        (Opposite.op K, ωA)), ωA) :=
  @asIso _ _ _ _ (dualizingBidualityMor.{u, v} A ωA K)
    (isIso_dualizingBidualityMor_of_finiteCohomology.{u, v} A ωA K hωA hK)

/-- **The canonical biduality morphism of [Stacks, Tag 0A7C] is natural in `K`.** -/
theorem dualizingBidualityIso_hom_naturality [IsNoetherianRing A]
    (ωA : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (hK' : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K'))
    (f : K ⟶ K') :
    f ≫ (dualizingBidualityIso.{u, v} ωA K' hωA hK').hom =
      (dualizingBidualityIso.{u, v} ωA K hωA hK).hom ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
          ((((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
                ((f.op, 𝟙 ωA) : (Opposite.op K', ωA) ⟶ (Opposite.op K, ωA))).op, 𝟙 ωA) :
            (Opposite.op ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
                (Opposite.op K, ωA)), ωA) ⟶
              (Opposite.op ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
                (Opposite.op K', ωA)), ωA)) :=
  bidualityMor_naturality _ ωA f

/-- **The five-step identification of Hom groups underlying [Stacks, Tag 0E9L].** -/
def dualityFormulaHomEquiv [IsNoetherianRing A]
    (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (hproj : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.obj ((derivedHomAdjunctionOverRing B).tensor.obj (F, E.functor.obj N)) ≅
        (derivedHomAdjunctionOverRing A).tensor.obj (iStar.obj F, N))
    (ωA K : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (Z : DerivedCategory (ModuleCat.{max u v} B)) :
    (Z ⟶ (derivedHom.{u, v, u} φ).obj K) ≃
      (Z ⟶ (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.obj
        (Opposite.op (E.functor.obj
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj (Opposite.op K, ωA))),
        (derivedHom.{u, v, u} φ).obj ωA)) where
  toFun b :=
    ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).homEquiv Z
        (E.functor.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
          (Opposite.op K, ωA))) ((derivedHom.{u, v, u} φ).obj ωA)).symm
      (adj.homEquiv _ ωA ((hproj _ Z).hom ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv (iStar.obj Z) _ ωA
          ((adj.homEquiv Z K).symm b ≫
            (dualizingBidualityIso.{u, v} ωA K hωA hK).hom)))
  invFun a := adj.homEquiv Z K
    (((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv (iStar.obj Z) _ ωA).symm
        ((hproj _ Z).inv ≫ (adj.homEquiv _ ωA).symm
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).homEquiv Z _ _ a)) ≫
      (dualizingBidualityIso.{u, v} ωA K hωA hK).inv)
  left_inv := by
    intro b
    simp only [AddEquiv.apply_symm_apply, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply, AddEquiv.symm_apply_apply, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  right_inv := by
    intro a
    simp only [Equiv.symm_apply_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      AddEquiv.apply_symm_apply, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply,
      AddEquiv.symm_apply_apply]

/-- The Hom-group identification of [Stacks, Tag 0E9L] is natural in the test object. -/
theorem dualityFormulaHomEquiv_naturality_source [IsNoetherianRing A]
    (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (hproj : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.obj ((derivedHomAdjunctionOverRing B).tensor.obj (F, E.functor.obj N)) ≅
        (derivedHomAdjunctionOverRing A).tensor.obj (iStar.obj F, N))
    (hprojNat : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      {F F' : DerivedCategory (ModuleCat.{max u v} B)} (f : F ⟶ F'),
      iStar.map ((derivedHomAdjunctionOverRing B).tensor.map
            (X := (F, E.functor.obj N)) (Y := (F', E.functor.obj N)) (f, 𝟙 (E.functor.obj N))) ≫
          (hproj N F').hom =
        (hproj N F).hom ≫ (derivedHomAdjunctionOverRing A).tensor.map
          (X := (iStar.obj F, N)) (Y := (iStar.obj F', N)) (iStar.map f, 𝟙 N))
    (ωA K : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    {Z Z' : DerivedCategory (ModuleCat.{max u v} B)} (g : Z' ⟶ Z)
    (b : Z ⟶ (derivedHom.{u, v, u} φ).obj K) :
    dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z' (g ≫ b) =
      g ≫ dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z b := by
  show ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).homEquiv _ _ _).symm _ = _
  rw [Adjunction.homEquiv_naturality_left_symm, Category.assoc,
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_naturality_left,
    reassoc_of% (hprojNat _ g).symm, Adjunction.homEquiv_naturality_left,
    homEquiv_symm_tensor_map_comp]
  rfl

/-- The Hom-group identification of [Stacks, Tag 0E9L] is natural in `K`. -/
theorem dualityFormulaHomEquiv_naturality_target [IsNoetherianRing A]
    (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (hproj : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.obj ((derivedHomAdjunctionOverRing B).tensor.obj (F, E.functor.obj N)) ≅
        (derivedHomAdjunctionOverRing A).tensor.obj (iStar.obj F, N))
    (hprojNatN : ∀ {N N' : DerivedCategory (ModuleCat.{max u v} A)} (n : N' ⟶ N)
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.map ((derivedHomAdjunctionOverRing B).tensor.map
            (X := (F, E.functor.obj N')) (Y := (F, E.functor.obj N))
            (𝟙 F, E.functor.map n)) ≫ (hproj N F).hom =
        (hproj N' F).hom ≫ (derivedHomAdjunctionOverRing A).tensor.map
          (X := (iStar.obj F, N')) (Y := (iStar.obj F, N)) (𝟙 (iStar.obj F), n))
    (ωA : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    {K K' : DerivedCategory (ModuleCat.{max u v} A)}
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (hK' : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K'))
    (f : K ⟶ K') (Z : DerivedCategory (ModuleCat.{max u v} B))
    (b : Z ⟶ (derivedHom.{u, v, u} φ).obj K) :
    dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K' hωA hK' Z
        (b ≫ (derivedHom.{u, v, u} φ).map f) =
      dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z b ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.map
          (((E.functor.map ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
              ((f.op, 𝟙 ωA) : (Opposite.op K', ωA) ⟶ (Opposite.op K, ωA)))).op,
            𝟙 ((derivedHom.{u, v, u} φ).obj ωA)) :
            (Opposite.op (E.functor.obj
                ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
                  (Opposite.op K, ωA))), (derivedHom.{u, v, u} φ).obj ωA) ⟶
              (Opposite.op (E.functor.obj
                ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
                  (Opposite.op K', ωA))), (derivedHom.{u, v, u} φ).obj ωA)) := by
  show ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).homEquiv _ _ _).symm _ = _
  rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc,
    dualizingBidualityIso_hom_naturality.{u, v} ωA hωA hK hK' f, ← Category.assoc,
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_dinaturality,
    reassoc_of% (hprojNatN _ Z).symm, Adjunction.homEquiv_naturality_left,
    homEquiv_symm_tensor_map_comp_middle]
  rfl

/-- **[Stacks, Tag 0E9L] for derived coextension of scalars, as an isomorphism of functors on
`D_Coh(A)`.** -/
def derivedHomNatIsoDualizingDerivedHom [IsNoetherianRing A]
    (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (hproj : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.obj ((derivedHomAdjunctionOverRing B).tensor.obj (F, E.functor.obj N)) ≅
        (derivedHomAdjunctionOverRing A).tensor.obj (iStar.obj F, N))
    (hprojNat : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      {F F' : DerivedCategory (ModuleCat.{max u v} B)} (f : F ⟶ F'),
      iStar.map ((derivedHomAdjunctionOverRing B).tensor.map
            (X := (F, E.functor.obj N)) (Y := (F', E.functor.obj N)) (f, 𝟙 (E.functor.obj N))) ≫
          (hproj N F').hom =
        (hproj N F).hom ≫ (derivedHomAdjunctionOverRing A).tensor.map
          (X := (iStar.obj F, N)) (Y := (iStar.obj F', N)) (iStar.map f, 𝟙 N))
    (hprojNatN : ∀ {N N' : DerivedCategory (ModuleCat.{max u v} A)} (n : N' ⟶ N)
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.map ((derivedHomAdjunctionOverRing B).tensor.map
            (X := (F, E.functor.obj N')) (Y := (F, E.functor.obj N))
            (𝟙 F, E.functor.map n)) ≫ (hproj N F).hom =
        (hproj N' F).hom ≫ (derivedHomAdjunctionOverRing A).tensor.map
          (X := (iStar.obj F, N')) (Y := (iStar.obj F, N)) (𝟙 (iStar.obj F), n))
    (ωA : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA) :
    (hasFiniteCohomology.{u, v} A).ι ⋙ derivedHom.{u, v, u} φ ≅
      (hasFiniteCohomology.{u, v} A).ι ⋙
        dualizingBaseChangeFunctor.{u, v} φ E ωA ((derivedHom.{u, v, u} φ).obj ωA) :=
  natIsoOfHomEquiv _ _
    (fun K Z =>
      dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K.obj hωA K.property Z)
    (fun K _ _ g a =>
      dualityFormulaHomEquiv_naturality_source.{u, v} φ E iStar adj hproj hprojNat ωA
        K.obj hωA K.property g a)
    (fun {K K'} f Z a =>
      dualityFormulaHomEquiv_naturality_target.{u, v} φ E iStar adj hproj hprojNatN ωA hωA
        K.property K'.property ((hasFiniteCohomology.{u, v} A).ι.map f) Z a)

/-- **[Stacks, Tag 0E9L] for a surjective `φ`, at its presentation with no variables.** Let
`φ : A →+* B` be a surjection of commutative rings with `A` Noetherian and let `ω_A` be a
dualizing complex for `A`.  Write `φ^!` for the algebraic upper shriek functor of the
presentation of `φ` by the polynomial algebra in no variables, put `ω_B = φ^!(ω_A)`,
`D_A(-) = RHom_A(-, ω_A)` and `D_B(-) = RHom_B(-, ω_B)`.  Then

`φ^!(K) ≅ D_B(D_A(K) ⊗_A^L B)`

*as an isomorphism of functors on `D_Coh(A)`*, which is what the source asserts.  Functoriality
rests on the projection formula of [Stacks, Tag 06Y6] being natural in both variables, which is
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso`; see the module docstring.

The same statement at an *arbitrary* presentation of the surjection `φ` is
`Dualizing.upperShriekFunctor_natIso_dualizingDerivedHom_of_surjective`, and for an arbitrary
finite-type `φ` it is
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_natIso_dualizingDerivedHom`. -/
noncomputable def upperShriekFunctor_ofSurjective_natIso_dualizingDerivedHom [IsNoetherianRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (ωA : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA) :
    (hasFiniteCohomology.{u, v} A).ι ⋙
        (PolynomialPresentation.ofSurjective φ hφ).upperShriekFunctor.{u, v} ≅
      (hasFiniteCohomology.{u, v} A).ι ⋙ dualizingBaseChangeFunctor.{u, v} φ E ωA
        ((PolynomialPresentation.ofSurjective φ hφ).upperShriekFunctor.{u, v}.obj ωA) :=
  let e := (upperShriekFunctor_ofSurjective_iso_derivedHom.{u, v} φ hφ).some
  Functor.isoWhiskerLeft _ e ≪≫
    derivedHomNatIsoDualizingDerivedHom.{u, v} φ E iStar adj
      (fun N F => (ProjectionFormula.derivedProjNatIso.{u, v} φ E iStar adj N).app F)
      (fun N {_ _} f =>
        (ProjectionFormula.derivedProjNatIso.{u, v} φ E iStar adj N).hom.naturality f)
      (fun {_ _} n F => NatTrans.congr_app
        ((ProjectionFormula.derivedProjBifunctorNatIso.{u, v} φ E iStar adj).hom.naturality n) F)
      ωA hωA ≪≫
    Functor.isoWhiskerLeft _
      (dualizingBaseChangeFunctorIsoOfIso.{u, v} φ E ωA (e.app ωA).symm)

/-- **[Stacks, Tag 0E9L] for derived coextension of scalars.** Let `φ : A →+* B` be a
homomorphism of commutative rings with `A` Noetherian, let `ω_A` be a dualizing complex for `A`
and let `K` have finite cohomology in every degree, i.e. lie in `D_Coh(A)`.  Put
`ω_B = RHom_A(B, ω_A)`, `D_A(-) = RHom_A(-, ω_A)` and `D_B(-) = RHom_B(-, ω_B)`.  Then

`RHom_A(B, K) ≅ D_B(D_A(K) ⊗_A^L B)` .

Here `i_*` is an arbitrary left adjoint of `RHom_A(B, -)` — derived restriction of scalars is
one, by [Stacks, Tag 0A70] — and the projection formula
`i_*(F ⊗_B^L (N ⊗_A^L B)) ≅ i_*F ⊗_A^L N` is carried as `hproj` together with its naturality
`hprojNat`.  Biduality is not assumed: it is supplied by
`Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`. -/
def derivedHomIsoDualizingDerivedHom [IsNoetherianRing A]
    (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (hproj : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      (F : DerivedCategory (ModuleCat.{max u v} B)),
      iStar.obj ((derivedHomAdjunctionOverRing B).tensor.obj (F, E.functor.obj N)) ≅
        (derivedHomAdjunctionOverRing A).tensor.obj (iStar.obj F, N))
    (hprojNat : ∀ (N : DerivedCategory (ModuleCat.{max u v} A))
      {F F' : DerivedCategory (ModuleCat.{max u v} B)} (f : F ⟶ F'),
      iStar.map ((derivedHomAdjunctionOverRing B).tensor.map
            (X := (F, E.functor.obj N)) (Y := (F', E.functor.obj N)) (f, 𝟙 (E.functor.obj N))) ≫
          (hproj N F').hom =
        (hproj N F).hom ≫ (derivedHomAdjunctionOverRing A).tensor.map
          (X := (iStar.obj F, N)) (Y := (iStar.obj F', N)) (iStar.map f, 𝟙 N))
    (ωA K : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    (derivedHom.{u, v, u} φ).obj K ≅
      (dualizingDerivedHomFunctor.{u, v} B ((derivedHom.{u, v, u} φ).obj ωA)).obj
        (Opposite.op (E.functor.obj
          ((dualizingDerivedHomFunctor.{u, v} A ωA).obj (Opposite.op K)))) :=
  Yoneda.ext _ _
    (fun {Z} b => dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z b)
    (fun {Z} a => (dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z).symm a)
    (fun {Z} b =>
      (dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z).symm_apply_apply b)
    (fun {Z} a =>
      (dualityFormulaHomEquiv.{u, v} φ E iStar adj hproj ωA K hωA hK Z).apply_symm_apply a)
    (fun {_ _} g b =>
      dualityFormulaHomEquiv_naturality_source.{u, v} φ E iStar adj hproj hprojNat ωA K hωA hK
        g b)

/-- **[Stacks, Tag 0E9L] for a surjective `φ`, at its presentation with no variables.** Let
`φ : A →+* B` be a surjection of commutative rings with `A` Noetherian, let `ω_A` be a dualizing
complex for `A` and let `K` lie in `D_Coh(A)`.  Write `φ^!` for the algebraic upper shriek
functor of the presentation of `φ` by the polynomial algebra in no variables, put
`ω_B = φ^!(ω_A)`, `D_A(-) = RHom_A(-, ω_A)` and `D_B(-) = RHom_B(-, ω_B)`.  Then

`φ^!(K) ≅ D_B(D_A(K) ⊗_A^L B)` .

This is the value at `K` of the functorial statement
`Dualizing.upperShriekFunctor_ofSurjective_natIso_dualizingDerivedHom`. -/
noncomputable def upperShriekFunctor_ofSurjective_iso_dualizingDerivedHom [IsNoetherianRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ derivedHom.{u, v, u} φ)
    (ωA K : DerivedCategory (ModuleCat.{max u v} A)) (hωA : IsDualizingComplex ωA)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    (PolynomialPresentation.ofSurjective φ hφ).upperShriekFunctor.{u, v}.obj K ≅
      (dualizingDerivedHomFunctor.{u, v} B
          ((PolynomialPresentation.ofSurjective φ hφ).upperShriekFunctor.{u, v}.obj ωA)).obj
        (Opposite.op (E.functor.obj
          ((dualizingDerivedHomFunctor.{u, v} A ωA).obj (Opposite.op K)))) :=
  (upperShriekFunctor_ofSurjective_natIso_dualizingDerivedHom.{u, v} φ hφ E iStar adj
    ωA hωA).app ⟨K, hK⟩

end

end Dualizing

end
