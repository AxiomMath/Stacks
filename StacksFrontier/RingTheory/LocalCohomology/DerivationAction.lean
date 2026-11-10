module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Cech.DerivationAction
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# A derivation of the base ring acting on local cohomology

Let `A` be a commutative ring, `I ⊂ A` a finitely generated ideal, `Z = V(I)` and `θ : A → A` a
derivation — modelled as `Derivation ℤ A A`. **Stacks 0EC5** asserts that `θ` induces canonical
additive operators `D : H^i_Z(A) → H^i_Z(A)` satisfying the Leibniz rule
`D (a x) = θ(a) x + a D(x)`.

The construction is the one of the source. Choose generators `f₁, …, f_r` of `I`. By the Čech
model of local cohomology (Stacks 0A6R) `RΓ_Z(A)` is computed by the extended alternating Čech
complex `C^•(f₁, …, f_r; A)`, each of whose terms is a direct sum of localizations of `A`, and
`θ` extends uniquely to each localization. Those extensions form an additive chain endomorphism
of the complex — `Cech.cechChainAction` — hence an additive operator on its cohomology, which
transports to `H^i_Z(A)` along the comparison.

Two things have to be pinned down for the operator to be *canonical* rather than merely existent.
First the comparison: `Stacks.LocalCohomology.cechComparisonInv` is not an arbitrary isomorphism
`C^•(f; A) ≅ RΓ_Z(A)` but the unique one carrying the counit of the adjunction defining local
cohomology to the Čech augmentation. Second the generators: the operator on `H^i_Z(A)` is
required to be computed by the Čech action *for every* finite generating family, which pins it
independently of the choice. That requirement is satisfiable because two generating families are
both subfamilies of their concatenation, and restriction to a subfamily preserves the
augmentation and commutes with the localization extensions.

The Leibniz rule alone does not determine the operator — two operators satisfying it differ by an
`A`-linear endomorphism of `H^i_Z(A)` — which is why the Čech characterization is part of the
data and not a corollary of it.

## Main definitions

* `Stacks.LocalCohomology.cechIso` — the normalized comparison at the ring.
* `Stacks.LocalCohomology.cechHomologyEquiv` — the identification `H^i(C^•(f; A)) ≃ H^i_Z(A)`
  it induces.
* `Stacks.LocalCohomology.transportedCechAction` — the Čech operator of `θ`, transported to
  `H^i_Z(A)`.
* `Stacks.LocalCohomology.DerivationOperator` — an additive operator on `H^i_Z(A)` with the
  twisted Leibniz rule and the Čech characterization.
* `Stacks.LocalCohomology.derivationOperator` — **Stacks 0EC5**, the canonical operator.

## Main results

* `Stacks.LocalCohomology.cechRestrict_augmentation` — restriction to a subfamily of the
  generators is compatible with the Čech augmentation.
* `Stacks.LocalCohomology.transportedCechAction_independent` — the transported operator does not
  depend on the generating family.
* `Stacks.LocalCohomology.DerivationOperator.ext` — the Čech characterization determines the
  operator.
* `Stacks.LocalCohomology.DerivationOperator.cech_apply` — on a Čech cohomology class, any
  operator on the complex satisfying the quotient rule computes the local-cohomology operator.
* `Stacks.LocalCohomology.derivationOperator_zero` — the zero derivation induces the zero
  operator. The Leibniz rule alone would not give this.

## Implementation notes

The comparisons appearing in `Stacks.LocalCohomology.cechHomologyEquiv_naturality` are ascribed
the `Stacks.LocalCohomology.extendedCechComplex` spelling of their source and target. Without
that, `rw` rejects the composites as not type-correct at `implicit` transparency, because
`HomologicalComplex.homologyFunctor` would have to be unfolded to match
`HomologicalComplex.homology`; ascribing the one spelling is what makes the rewrites legal.

## References

* [Stacks Project, Tag 0EC5](https://stacks.math.columbia.edu/tag/0EC5)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
-/

@[expose] public noncomputable section

open CategoryTheory
open ExtendedAlternatingCech (Idx)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {r : ℕ}

/-! ### The normalized comparison at the ring -/

/-- **The normalized comparison at the ring**: the unique isomorphism from the Čech object of a
generating family of `I` to the value of `RΓ_{V(I)}` at `A` that carries the counit of the
local-cohomology adjunction to the Čech augmentation. -/
def cechIso (f : Fin r → A) (I : Ideal A) (hI : I.FG) (hf : Ideal.span (Set.range f) = I) :
    extendedCechObject f (ModuleCat.of A A) ≅
      (localCohomologyOnModules A I hI).obj (ModuleCat.of A A) :=
  ((localCohomologyIsoCech f I hI hf).app (ModuleCat.of A A)).symm

/-- The normalization of `Stacks.LocalCohomology.cechIso`. -/
theorem cechIso_hom_comp_counit (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) :
    (cechIso f I hI hf).hom ≫ (localCohomologyCounit I hI).app (ModuleCat.of A A) =
      (cechAugmentationHom f).app (ModuleCat.of A A) :=
  cechComparisonInv_comp_counit f I hI hf (ModuleCat.of A A)

/-- **The comparison is natural over the augmentation.** A map of Čech objects compatible with
the two augmentations is compatible with the two comparisons; this is uniqueness of the
normalized comparison. -/
theorem cechIso_naturality (f : Fin r → A) {s : ℕ} (g : Fin s → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (k : extendedCechComplex f (ModuleCat.of A A) ⟶ extendedCechComplex g (ModuleCat.of A A))
    (hk : DerivedCategory.Q.map k ≫ (cechAugmentationHom g).app (ModuleCat.of A A) =
      (cechAugmentationHom f).app (ModuleCat.of A A)) :
    DerivedCategory.Q.map k ≫ (cechIso g I hI hg).hom = (cechIso f I hI hf).hom := by
  refine (bijective_comp_localCohomologyCounit_app I hI (ModuleCat.of A A) _
    (derivedPowerTorsionProperty_extendedCechObject f (ModuleCat.of A A) I hI hf)).injective ?_
  rw [Category.assoc, cechIso_hom_comp_counit, hk, cechIso_hom_comp_counit]

/-- **The identification of Čech cohomology with local cohomology** in a fixed degree. -/
def cechHomologyEquiv (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (i : ℕ) :
    (Cech.cechComplex f A).homology i ≃ₗ[A]
      localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ) :=
  ((HomologicalComplex.extendHomologyIso (Cech.cechComplex f A)
        ComplexShape.embeddingUpNat (j := i) (j' := (i : ℤ)) (by simp)).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (i : ℤ)).app
        (extendedCechComplex f (ModuleCat.of A A))).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)).mapIso
        (cechIso f I hI hf)).toLinearEquiv

/-- A chain map compatible with the Čech augmentations is compatible with the augmentations in
the derived category. -/
theorem Q_map_comp_extendedCechAugmentationHom {f : Fin r → A} {s : ℕ} {g : Fin s → A}
    (k : Cech.cechComplex f A ⟶ Cech.cechComplex g A)
    (hk : HomologicalComplex.extendMap k ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation g (ModuleCat.of A A) =
      extendedCechAugmentation f (ModuleCat.of A A)) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat) ≫
        extendedCechAugmentationHom g (ModuleCat.of A A) =
      extendedCechAugmentationHom f (ModuleCat.of A A) := by
  rw [extendedCechAugmentationHom, extendedCechAugmentationHom, ← Category.assoc,
    ← Functor.map_comp, hk]

/-- **The comparison is natural on cohomology.** -/
theorem cechHomologyEquiv_naturality {f : Fin r → A} {s : ℕ} {g : Fin s → A} (I : Ideal A)
    (hI : I.FG) (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (k : Cech.cechComplex f A ⟶ Cech.cechComplex g A)
    (hk : HomologicalComplex.extendMap k ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation g (ModuleCat.of A A) =
      extendedCechAugmentation f (ModuleCat.of A A))
    (i : ℕ) (x : (Cech.cechComplex f A).homology i) :
    cechHomologyEquiv g I hI hg i (HomologicalComplex.homologyMap k i x) =
      cechHomologyEquiv f I hI hf i x := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i : ℤ)
  let q : extendedCechComplex f (ModuleCat.of A A) ⟶ extendedCechComplex g (ModuleCat.of A A) :=
    HomologicalComplex.extendMap k ComplexShape.embeddingUpNat
  let a : (extendedCechComplex f (ModuleCat.of A A)).homology (i : ℤ) ≅
      (Cech.cechComplex f A).homology i :=
    (Cech.cechComplex f A).extendHomologyIso ComplexShape.embeddingUpNat
      (j := i) (j' := (i : ℤ)) (by simp)
  let b : (extendedCechComplex g (ModuleCat.of A A)).homology (i : ℤ) ≅
      (Cech.cechComplex g A).homology i :=
    (Cech.cechComplex g A).extendHomologyIso ComplexShape.embeddingUpNat
      (j := i) (j' := (i : ℤ)) (by simp)
  let c : H.obj (DerivedCategory.Q.obj (extendedCechComplex f (ModuleCat.of A A))) ≅
      (extendedCechComplex f (ModuleCat.of A A)).homology (i : ℤ) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (i : ℤ)).app
      (extendedCechComplex f (ModuleCat.of A A))
  let d : H.obj (DerivedCategory.Q.obj (extendedCechComplex g (ModuleCat.of A A))) ≅
      (extendedCechComplex g (ModuleCat.of A A)).homology (i : ℤ) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (i : ℤ)).app
      (extendedCechComplex g (ModuleCat.of A A))
  have hnat : HomologicalComplex.homologyMap q (i : ℤ) ≫ b.hom =
      a.hom ≫ HomologicalComplex.homologyMap k i :=
    HomologicalComplex.extendHomologyIso_hom_naturality k ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f i = (i : ℤ) by simp)
  have inv_nat : ∀ {X Y X' Y' : ModuleCat.{u} A} (a : X ≅ X') (b : Y ≅ Y') (u : X ⟶ Y)
      (u' : X' ⟶ Y'), u ≫ b.hom = a.hom ≫ u' → u' ≫ b.inv = a.inv ≫ u := fun a b u u' h => by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  have ha := inv_nat a b _ _ hnat
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (i : ℤ)).hom.naturality q
  change H.map (DerivedCategory.Q.map q) ≫ d.hom =
    c.hom ≫ HomologicalComplex.homologyMap q (i : ℤ) at hn
  have hb := inv_nat c d _ _ hn
  have he := cechIso_naturality f g I hI hf hg q (Q_map_comp_extendedCechAugmentationHom k hk)
  have h : HomologicalComplex.homologyMap k i ≫
        b.inv ≫ d.inv ≫ H.map (cechIso g I hI hg).hom =
      a.inv ≫ c.inv ≫ H.map (cechIso f I hI hf).hom := by
    rw [← Category.assoc, ha, Category.assoc,
      ← Category.assoc (HomologicalComplex.homologyMap q (i : ℤ)), hb]
    simp only [Category.assoc]
    rw [← H.map_comp, he]
  exact congrArg (fun u => u x) h

/-! ### Restriction to a subfamily preserves the augmentation -/

variable {s : ℕ}

/-- **Restriction to a subfamily of the generators is compatible with the augmentation.** Both
degree-zero terms are the single summand indexed by the empty set, on which the restriction map
is the identity of `A`. -/
theorem cechRestrict_augmentation (f : Fin r → A) (g : Fin s → A) (e : Fin r ↪o Fin s)
    (he : ∀ i, g (e i) = f i) :
    HomologicalComplex.extendMap (Cech.cechRestrict f A g e he) ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation f (ModuleCat.of A A) =
      extendedCechAugmentation g (ModuleCat.of A A) := by
  have haug : ∀ {n : ℕ} (u : Fin n → A),
      (extendedCechAugmentation u (ModuleCat.of A A)).f 0 =
        (HomologicalComplex.extendXIso (Cech.cechComplex u A) ComplexShape.embeddingUpNat
            ComplexShape.embeddingUpNat_f_zero).hom ≫
          (cechZeroIso u (ModuleCat.of A A)).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv := by
    intro n u
    rw [extendedCechAugmentation_f_zero]
    change ((HomologicalComplex.extendXIso (Cech.cechComplex u A) ComplexShape.embeddingUpNat
      ComplexShape.embeddingUpNat_f_zero).hom ≫ (cechZeroIso u (ModuleCat.of A A)).hom) ≫ _ = _
    rw [Category.assoc]
  have hzero : (Cech.cechRestrict f A g e he).f 0 ≫
      (cechZeroIso f (ModuleCat.of A A)).hom = (cechZeroIso g (ModuleCat.of A A)).hom := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨m, rfl⟩ := (cechTermZeroEquiv g (ModuleCat.of A A)).symm.surjective x
    change cechTermZeroEquiv f (ModuleCat.of A A)
        (Cech.cechTermRestrict f A g e he 0
          ((cechTermZeroEquiv g (ModuleCat.of A A)).symm m)) =
      cechTermZeroEquiv g (ModuleCat.of A A)
        ((cechTermZeroEquiv g (ModuleCat.of A A)).symm m)
    rw [LinearEquiv.apply_symm_apply, cechTermZeroEquiv_symm_apply,
      Cech.cechTermRestrict_lof_zero, cechTermZeroEquiv_lof,
        Stacks.CechBaseChange.cechModEmptyEquiv_mk]
  have hzero' : (Cech.cechRestrict f A g e he).f 0 ≫
      (cechZeroIso f (ModuleCat.of A A)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv =
      (cechZeroIso g (ModuleCat.of A A)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv := by
    rw [← Category.assoc, hzero]
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero,
    haug f, haug g]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hzero']

/-! ### The operator on local cohomology -/

/-- The Čech operator of a derivation, transported to local cohomology along the normalized
comparison attached to a generating family. -/
def transportedCechAction (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (θ : Derivation ℤ A A) (i : ℕ) :
    localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ) →+
      localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ) :=
  (cechHomologyEquiv f I hI hf i).toAddMonoidHom.comp
    ((Cech.cechHomologyAction f θ i).comp (cechHomologyEquiv f I hI hf i).symm.toAddMonoidHom)

/-- The transported operator, read on a class coming from Čech cohomology. -/
theorem transportedCechAction_apply (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (θ : Derivation ℤ A A) (i : ℕ)
    (x : (Cech.cechComplex f A).homology i) :
    transportedCechAction f I hI hf θ i (cechHomologyEquiv f I hI hf i x) =
      cechHomologyEquiv f I hI hf i (Cech.cechHomologyAction f θ i x) := by
  change cechHomologyEquiv f I hI hf i (Cech.cechHomologyAction f θ i
    ((cechHomologyEquiv f I hI hf i).symm (cechHomologyEquiv f I hI hf i x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The transported operator satisfies the twisted Leibniz rule. -/
theorem transportedCechAction_leibniz (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (θ : Derivation ℤ A A) (i : ℕ) (a : A)
    (x : localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ)) :
    transportedCechAction f I hI hf θ i (a • x) =
      θ a • x + a • transportedCechAction f I hI hf θ i x := by
  change cechHomologyEquiv f I hI hf i (Cech.cechHomologyAction f θ i
      ((cechHomologyEquiv f I hI hf i).symm (a • x))) =
    θ a • x + a • cechHomologyEquiv f I hI hf i
      (Cech.cechHomologyAction f θ i ((cechHomologyEquiv f I hI hf i).symm x))
  simp only [map_smul, Cech.cechHomologyAction_leibniz, map_add, LinearEquiv.apply_symm_apply]

/-- **The transported operator does not depend on the chain map used to compare two generating
families**, as long as that map preserves the augmentation and commutes with the Čech action. -/
theorem transportedCechAction_naturality {f : Fin r → A} {g : Fin s → A} (I : Ideal A)
    (hI : I.FG) (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (θ : Derivation ℤ A A) (k : Cech.cechComplex f A ⟶ Cech.cechComplex g A)
    (hk : HomologicalComplex.extendMap k ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation g (ModuleCat.of A A) =
      extendedCechAugmentation f (ModuleCat.of A A))
    (hact : ∀ (p : ℕ) (x : Cech.cechTerm f A p),
      k.f p (Cech.cechTermAction f θ p x) = Cech.cechTermAction g θ p (k.f p x))
    (i : ℕ) : transportedCechAction f I hI hf θ i = transportedCechAction g I hI hg θ i := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (cechHomologyEquiv f I hI hf i).surjective x
  have hn := cechHomologyEquiv_naturality I hI hf hg k hk i
  rw [transportedCechAction_apply, ← hn y, transportedCechAction_apply,
    Cech.cechHomologyAction_naturality f g θ k hact i y, hn]

/-- The concatenation of two generating families of `I` generates `I`. -/
theorem span_append_generators (f : Fin r → A) (g : Fin s → A) (I : Ideal A)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I) :
    Ideal.span (Set.range (Fin.append f g)) = I := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro a ⟨j, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left, ← hf] using
        Ideal.subset_span (show f j ∈ Set.range f from ⟨j, rfl⟩)
    · simpa only [Fin.append_right, ← hg] using
        Ideal.subset_span (show g j ∈ Set.range g from ⟨j, rfl⟩)
  · rw [← hf]
    refine Ideal.span_mono ?_
    rintro a ⟨j, rfl⟩
    exact ⟨Fin.castAdd s j, Fin.append_left f g j⟩

/-- **The transported operator is independent of the generating family.** Both families are
subfamilies of their concatenation, and restriction to a subfamily preserves the augmentation and
commutes with the Čech action. -/
theorem transportedCechAction_independent {f : Fin r → A} {g : Fin s → A} (I : Ideal A)
    (hI : I.FG) (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (θ : Derivation ℤ A A) (i : ℕ) :
    transportedCechAction f I hI hf θ i = transportedCechAction g I hI hg θ i := by
  let h := Fin.append f g
  have hspan := span_append_generators f g I hf hg
  let el := Fin.castAddOrderEmb (n := r) s
  let er := Fin.natAddOrderEmb (m := s) r
  have hl : ∀ j, h (el j) = f j := fun j => Fin.append_left f g j
  have hr : ∀ j, h (er j) = g j := fun j => Fin.append_right f g j
  exact (transportedCechAction_naturality I hI hspan hf θ (Cech.cechRestrict f A h el hl)
    (cechRestrict_augmentation f h el hl) (Cech.cechTermRestrict_action f h el hl θ) i).symm.trans
    (transportedCechAction_naturality I hI hspan hg θ (Cech.cechRestrict g A h er hr)
      (cechRestrict_augmentation g h er hr) (Cech.cechTermRestrict_action g h er hr θ) i)

/-- **An additive operator on local cohomology induced by a derivation of the ring.** The data is
the operator; the conditions are the twisted Leibniz rule and the requirement that, for *every*
finite generating family of `I`, the operator is computed on Čech cohomology classes by the
localization extensions of the derivation.

The Čech condition is what makes the operator canonical. -/
structure DerivationOperator (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (i : ℕ)
    (θ : Derivation ℤ A A) where
  /-- The underlying additive operator on `H^i_{V(I)}(A)`. -/
  toAddMonoidHom : localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ) →+
    localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ)
  /-- **The twisted Leibniz rule.** -/
  leibniz (a : A) (x : localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ)) :
    toAddMonoidHom (a • x) = θ a • x + a • toAddMonoidHom x
  /-- **The Čech characterization**, for every finite generating family of `I`. -/
  cech {n : ℕ} (f : Fin n → A) (hf : Ideal.span (Set.range f) = I)
      (z : (Cech.cechComplex f A).cycles i) :
    toAddMonoidHom
        (cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i z)) =
      cechHomologyEquiv f I hI hf i
        ((Cech.cechComplex f A).homologyπ i (Cech.cechCyclesAction f θ i z))

/-- Every element of local cohomology comes from a Čech cycle of a generating family. -/
private theorem exists_cechHomologyEquiv_homologyπ {f : Fin r → A} {I : Ideal A} {hI : I.FG}
    (hf : Ideal.span (Set.range f) = I) (i : ℕ)
    (x : localCohomologyModule A I hI (ModuleCat.of A A) (i : ℤ)) :
    ∃ z : (Cech.cechComplex f A).cycles i,
      cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i z) = x := by
  obtain ⟨y, rfl⟩ := (cechHomologyEquiv f I hI hf i).surjective x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi ((Cech.cechComplex f A).homologyπ i)) y
  exact ⟨z, rfl⟩

/-- **The Čech characterization determines the operator.** -/
theorem DerivationOperator.ext {I : Ideal A} {hI : I.FG} {i : ℕ} {θ : Derivation ℤ A A}
    (D E : DerivationOperator A I hI i θ) : D = E := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have heq : D.toAddMonoidHom = E.toAddMonoidHom := by
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := exists_cechHomologyEquiv_homologyπ hf i x
    rw [D.cech f hf z, E.cech f hf z]
  cases D
  cases E
  cases heq
  rfl

/-- **Any operator on the Čech complex obeying the quotient rule computes the local-cohomology
operator** on cohomology classes. The hypothesis says that `w` is a cycle representing the image
of `z` under the Čech operator. -/
theorem DerivationOperator.cech_apply {I : Ideal A} {hI : I.FG} {i : ℕ}
    {θ : Derivation ℤ A A} (D : DerivationOperator A I hI i θ) {f : Fin r → A}
    (hf : Ideal.span (Set.range f) = I) (δ : Cech.DerivationAction f θ)
    (z w : (Cech.cechComplex f A).cycles i)
    (hw : (Cech.cechComplex f A).iCycles i w =
      δ.toAddMonoidHom i ((Cech.cechComplex f A).iCycles i z)) :
    D.toAddMonoidHom (cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i z)) =
      cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i w) := by
  obtain rfl := Cech.DerivationAction.ext f δ (Cech.derivationAction f θ)
  obtain rfl : w = Cech.cechCyclesAction f θ i z :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstance : Mono ((Cech.cechComplex f A).iCycles i))
      (hw.trans (Cech.cechCyclesAction_i f θ i z).symm)
  exact D.cech f hf z

/-- **The canonical operator exists.** -/
theorem nonempty_derivationOperator (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (θ : Derivation ℤ A A) (i : ℕ) : Nonempty (DerivationOperator A I hI i θ) := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  exact ⟨{ toAddMonoidHom := transportedCechAction f I hI hf θ i
           leibniz := transportedCechAction_leibniz f I hI hf θ i
           cech := fun g hg z => by
             rw [transportedCechAction_independent I hI hf hg θ i, transportedCechAction_apply,
               Cech.cechHomologyAction_π] }⟩

/-- **Stacks Project, Tag 0EC5.** A derivation `θ` of `A` induces a canonical additive operator on
each local cohomology module `H^i_{V(I)}(A)`, satisfying the Leibniz rule
`D (a x) = θ(a) x + a D(x)`. It is characterized on Čech cohomology classes by the unique
extensions of `θ` to the localizations appearing in the Čech complex, for every finite generating
family of `I`; `Stacks.LocalCohomology.DerivationOperator.ext` is the uniqueness this
characterization provides. -/
@[stacks 0EC5]
def derivationOperator (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (θ : Derivation ℤ A A) (i : ℕ) : DerivationOperator A I hI i θ :=
  Classical.choice (nonempty_derivationOperator A I hI θ i)

/-- The canonical operator is computed by the localization extensions of `θ` on every Čech
cohomology class. -/
theorem derivationOperator_cech (I : Ideal A) (hI : I.FG) (θ : Derivation ℤ A A) (i : ℕ)
    {f : Fin r → A} (hf : Ideal.span (Set.range f) = I) (δ : Cech.DerivationAction f θ)
    (z w : (Cech.cechComplex f A).cycles i)
    (hw : (Cech.cechComplex f A).iCycles i w =
      δ.toAddMonoidHom i ((Cech.cechComplex f A).iCycles i z)) :
    (derivationOperator A I hI θ i).toAddMonoidHom
        (cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i z)) =
      cechHomologyEquiv f I hI hf i ((Cech.cechComplex f A).homologyπ i w) :=
  (derivationOperator A I hI θ i).cech_apply hf δ z w hw

/-- **The zero derivation induces the zero operator**, in every ring, support and degree. The
Leibniz rule alone would not imply this. -/
theorem derivationOperator_zero (I : Ideal A) (hI : I.FG) (i : ℕ) :
    (derivationOperator A I hI 0 i).toAddMonoidHom = 0 := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨z, rfl⟩ := exists_cechHomologyEquiv_homologyπ hf i x
  simpa using (derivationOperator A I hI 0 i).cech_apply hf
    (Cech.DerivationAction.zero f) z 0 (map_zero _)

end Stacks.LocalCohomology

end
