module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeDividedPowerPolynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialThickeningFunctor

/-!
# The rows of the Čech–de Rham double complex over a base with zero divided power ideal

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `p` nilpotent in
`A = Γ(S, 𝒪_S)`, `X` separated, a family `U_i` of affine opens of `X` and smooth lifts `B_i` of
them carrying étale coordinates, with objects `D_i = (U_i, Spec B_i, γ_i)` of `Cris(X/S)`.  For a
quasi-coherent module `N` on `CRIS(X/S)` there are two Čech–de Rham double complexes: that of the
cover by the `D_i`,

`B^a(⦋n⦌) = ∏_{x : Fin (n + 1) → ι} N(D_x) ⊗ Ω^a_{D_x}`

(`CechEnvelope.cechDeRhamDoubleComplex`), and that of the cover of `X` by the trivial thickenings
`(U_i, U_i, 0)` (`Crystalline.GlobalCrystallineSituation.trivialThickeningFunctor`),

`C^a(⦋n⦌) = ∏_x N(U_x, U_x, 0) ⊗ Ω^a_{Γ(U_x)/A}`, `U_x = U_{x 0} ∩ ⋯ ∩ U_{x n}`

(`CechEnvelope.trivialCechDeRhamDoubleComplex`).  The closed immersions `(U_i, U_i, 0) ⟶ D_i`
(`CechEnvelope.trivialChartHom`) induce a map `B ⟶ C` (`CechEnvelope.trivialRowHom`).

When the divided power ideal `I` of `A` is zero this map is a quasi-isomorphism on every row
(`CechEnvelope.quasiIso_rowMap_trivialRowHom`), hence induces isomorphisms on the cohomology of the
total complexes (`CechEnvelope.trivialRowsHomologyIso`).  On the factor indexed by `x`, the map
`(U_x, U_x, 0) ⟶ D_x` has a retraction `D_x ⟶ (U_x, U_x, 0)`: the envelope `Γ(D_x)` is a divided
power polynomial algebra over `Γ(U_x)` along a section `σ` of its augmentation
(`CechEnvelope.exists_dpPolynomial_equiv_envelope_of_ideal_eq_bot`), and `σ` is the retraction on
global sections (`CechEnvelope.trivialRetraction`).  The retraction induces a quasi-isomorphism of
de Rham complexes by the transported [Stacks, Tag 07LD]
(`Crystalline.GlobalCrystallineSituation.quasiIso_crystalDeRhamPresheaf_map`), and the composite
`(U_x, U_x, 0) ⟶ D_x ⟶ (U_x, U_x, 0)` is the identity, as every endomorphism of a trivial
thickening over an open of `X` is (`CechEnvelope.trivialThickeningFunctor_hom_ext`); so the
comparison is a quasi-isomorphism by two out of three.

## Main definitions

* `CechEnvelope.trivialChartHom` — the closed immersion `(U_i, U_i, 0) ⟶ D_i`.
* `CechEnvelope.trivialCechDeRhamDoubleComplex` — the Čech–de Rham double complex of the cover of
  `X` by the trivial thickenings of the `U_i`.
* `CechEnvelope.trivialRowHom` — the comparison `B ⟶ C`.
* `CechEnvelope.trivialRetraction` — the retraction `D_x ⟶ (U_x, U_x, 0)` of a section `σ`.
* `CechEnvelope.trivialRowsHomologyIso` — the induced isomorphisms on the cohomology of the total
  complexes, over a base with zero divided power ideal.

## Main results

* `CechEnvelope.quasiIso_map_interComparison` — on the factor indexed by `x` the comparison is a
  quasi-isomorphism.
* `CechEnvelope.quasiIso_rowMap_trivialRowHom` — the comparison is a quasi-isomorphism on every
  row.

## References

* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DividedPowers

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite Stacks.CechSite.FinalCover Crystalline.CosimplicialDoubleComplex

/-! ### Generalities -/

section Generalities

/-- A divided power structure sends `0` to `1` in degree `0` and to `0` in positive degrees. -/
private theorem dpow_zero_eq_ite {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    (n : ℕ) : hI.dpow n 0 = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, hI.dpow_zero I.zero_mem]
  · exact hI.dpow_eval_zero h

/-- **A ring map out of a ring with zero divided power ideal is a divided power morphism.** -/
theorem isDPMorphism_of_ideal_eq_bot {A B : Type*} [CommSemiring A] [CommSemiring B]
    {I : Ideal A} {J : Ideal B} (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B)
    (h0 : I = ⊥) : IsDPMorphism hI hJ f where
  ideal_comp := by
    rw [h0, Ideal.map_bot]
    exact bot_le
  dpow_comp {n} a ha := by
    rw [h0, Ideal.mem_bot] at ha
    subst ha
    rw [map_zero, dpow_zero_eq_ite, dpow_zero_eq_ite, apply_ite f, map_one, map_zero]

/-- The divided power structure on the zero ideal is unique. -/
theorem dividedPowers_bot_eq {R : Type*} [CommRing R] (γ δ : DividedPowers (⊥ : Ideal R)) :
    γ = δ :=
  DividedPowers.ext γ δ fun n x hx ↦ by
    rw [Ideal.mem_bot.mp hx, dpow_zero_eq_ite, dpow_zero_eq_ite]

/-- **The divided power polynomial algebra over a ring with zero divided power ideal does not
depend on how the zero ideal is spelled**, as a source of divided power morphisms. -/
theorem isDPMorphism_polyRing_source_of_eq_bot {R : Type u} [CommRing R] {I J : Ideal R}
    (hI : I = ⊥) (hJ : J = ⊥) (γ : DividedPowers I) (δ : DividedPowers J) (W : Type u)
    {C : Type u} [CommRing C] {K : Ideal C} (hK : DividedPowers K)
    (f : DividedPowerAlgebra R (W →₀ R) →+* C)
    (hf : IsDPMorphism (DeRhamPair.polyRing (.of R I γ) W).dividedPowers hK f) :
    IsDPMorphism (DeRhamPair.polyRing (.of R J δ) W).dividedPowers hK f := by
  subst hI hJ
  obtain rfl := dividedPowers_bot_eq γ δ
  exact hf

/-- **The divided power polynomial algebra over a ring with zero divided power ideal does not
depend on how the zero ideal is spelled**, as a target of divided power morphisms. -/
theorem isDPMorphism_polyRing_target_of_eq_bot {R : Type u} [CommRing R] {I J : Ideal R}
    (hI : I = ⊥) (hJ : J = ⊥) (γ : DividedPowers I) (δ : DividedPowers J) (W : Type u)
    {C : Type u} [CommRing C] {K : Ideal C} (hK : DividedPowers K)
    (f : C →+* DividedPowerAlgebra R (W →₀ R))
    (hf : IsDPMorphism hK (DeRhamPair.polyRing (.of R I γ) W).dividedPowers f) :
    IsDPMorphism hK (DeRhamPair.polyRing (.of R J δ) W).dividedPowers f := by
  subst hI hJ
  obtain rfl := dividedPowers_bot_eq γ δ
  exact hf

variable {S : GlobalCrystallineSituation.{u}}

/-- **Two morphisms of `CRIS(X/S)` out of a trivial thickening `(V, V, 0)` agree** as soon as the
map of the target to `X` is a monomorphism: the map on thickened schemes is a map over `X`, and
the map on ambient schemes is the map on thickened schemes followed by the immersion. -/
theorem free_obj_hom_ext {V : Over S.X} {T : Thickening S} [Mono T.toX]
    (f g : (free S).obj V ⟶ T) : f = g := by
  have hs : f.sourceHom = g.sourceHom :=
    (cancel_mono T.toX).1 (f.toX_naturality.trans g.toX_naturality.symm)
  have hf : 𝟙 V.left ≫ f.targetHom.hom = f.sourceHom ≫ T.thickening.immersion :=
    f.immersion_naturality
  have hg : 𝟙 V.left ≫ g.targetHom.hom = g.sourceHom ≫ T.thickening.immersion :=
    g.immersion_naturality
  refine Thickening.Hom.ext hs (DividedPowerScheme.Hom.ext ?_)
  exact (Category.id_comp _).symm.trans
    ((hf.trans ((congrArg (· ≫ _) hs).trans hg.symm)).trans (Category.id_comp _))

/-- **Two morphisms of `AffineCris S` out of the trivial thickening of an affine open agree**:
the target lies in `Cris(X/S)`, so its map to `X` is an open immersion. -/
theorem trivialThickeningFunctor_hom_ext {V : AffineOpens S.X} {T : AffineCris S}
    (f g : (trivialThickeningFunctor S).obj V ⟶ T) : f = g := by
  have : IsOpenImmersion T.obj.obj.toX := T.obj.property
  exact ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (free_obj_hom_ext (V := Over.mk V.obj.ι) f.hom.hom g.hom.hom))

/-- The trivial divided power scheme of an affine scheme is affine. -/
instance isAffine_trivialDividedPowerScheme (Y : Scheme.{u}) [IsAffine Y] :
    IsAffine (trivialDividedPowerScheme Y).scheme :=
  ‹IsAffine Y›

/-- The affine open `U_i` of a family of affine opens, as an object of `AffineOpens X`. -/
abbrev chartOpen {ι : Type} (U : ι → S.X.Opens) [∀ i, IsAffine (U i)] (i : ι) :
    AffineOpens S.X :=
  ⟨U i, inferInstanceAs (IsAffine (U i))⟩

end Generalities

/-! ### The comparison of double complexes -/

section Comparison

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

/-- The identification `U_i ≅ Spec (B_i / I B_i)` of `U_i` with the thickened scheme of `D_i`. -/
def trivialChartSourceHom (i : ι) : (U i).toScheme ⟶ ((L i).object hp).thickening.source :=
  inv (I := (L i).isIso_specToX hp)
    (specToX (isNilpotent_prime_over S (U i).ι hp) ((L i).thickening hp))

omit [S.X.IsSeparated] in
/-- `trivialChartSourceHom` is a map over `X`. -/
theorem trivialChartSourceHom_toX (i : ι) :
    trivialChartSourceHom hp L i ≫ ((L i).object hp).toX = (U i).ι := by
  rw [SmoothLift.object_toX]
  exact @IsIso.inv_hom_id_assoc _ _ _ _
    (specToX (isNilpotent_prime_over S (U i).ι hp) ((L i).thickening hp))
    ((L i).isIso_specToX hp) _ (U i).ι

/-- **The closed immersion `(U_i, U_i, 0) ⟶ D_i = (U_i, Spec B_i, γ_i)`** of the trivial
thickening of `U_i` into the object of the smooth lift `B_i`: on thickened schemes it is the
identification `U_i ≅ Spec (B_i / I B_i)`, and on ambient schemes it is followed by the closed
immersion `Spec (B_i / I B_i) ⟶ Spec B_i`, i.e. on rings `B_i → B_i / I B_i ≅ Γ(U_i)`. -/
def trivialChartHom (i : ι) :
    (trivialThickeningFunctor S).obj (chartOpen U i) ⟶ affineObject hp L i :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (((freeForgetAdjunction S).homEquiv (Over.mk (U i).ι) ((L i).object hp)).symm
      (Over.homMk (trivialChartSourceHom hp L i) (trivialChartSourceHom_toX hp L i))))

/-- **The Čech–de Rham double complex of the cover of `X` by the trivial thickenings
`(U_i, U_i, 0)`**: `C^a(⦋n⦌) = ∏_x N(U_x, U_x, 0) ⊗ Ω^a_{Γ(U_x)/A}`, for a quasi-coherent module
`N` on `CRIS(X/S)`, `U_x` running over the intersections `U_{x 0} ∩ ⋯ ∩ U_{x n}`. -/
def trivialCechDeRhamDoubleComplex (U : ι → S.X.Opens) [∀ i, IsAffine (U i)]
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite) :
    CochainComplex (CosimplicialObject (ModuleCat.{u} Γ(S.S.scheme, ⊤))) ℕ :=
  doubleComplex (chartOpen U) ((trivialThickeningFunctor S).op ⋙ bigCrystalDeRhamPresheaf hN)

/-- **The comparison `B ⟶ C` of Čech–de Rham double complexes** induced by the closed immersions
`(U_i, U_i, 0) ⟶ D_i`: on the factor indexed by a tuple `x`, the restriction along
`(U_x, U_x, 0) ⟶ D_x`. -/
def trivialRowHom (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (hN : N.IsQuasicoherentOnSite) :
    cechDeRhamDoubleComplex hp L N hN ⟶ trivialCechDeRhamDoubleComplex U N hN :=
  (doubleComplexComparison _ (trivialThickeningFunctor S) (trivialChartHom hp L)).app
    (bigCrystalDeRhamPresheaf hN)

end Comparison

/-! ### The retraction of the envelope onto the intersection -/

section Retraction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {n : ℕ}
  {U : Fin (n + 1) → S.X.Opens} [∀ k, IsAffine (U k)] (L : ∀ k, SmoothLift S (U k).ι)

attribute [local instance] interAlgebra

/-- The intersection `U_0 ∩ ⋯ ∩ U_n`, as an affine open. -/
abbrev interAffineOpen (U : Fin (n + 1) → S.X.Opens) [∀ k, IsAffine (U k)] : AffineOpens S.X :=
  ⟨inter U, isAffine_inter U⟩

/-- The envelope object `D_s = (U_0 ∩ ⋯ ∩ U_n, Spec D, δ)`, as an object of `AffineCris S`. -/
def envelopeAffine : AffineCris S :=
  ⟨⟨envelopeObject hp L, inferInstance⟩, inferInstance⟩

/-- The ambient scheme of the trivial thickening of the intersection is affine. -/
instance isAffine_free_inter_target :
    IsAffine ((free S).obj (Over.mk (inter U).ι)).thickening.target.scheme :=
  isAffine_inter U

/-- The map `Γ(U_0 ∩ ⋯ ∩ U_n) → D → Γ(Spec D, ⊤)` of a ring map `σ`, as a divided power morphism
out of the zero divided power ideal. -/
def retractionSectionsMap (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object) :
    ((free S).obj (Over.mk (inter U).ι)).thickening.target.dividedPowers.toDividedPowerRing
        (op ⊤) ⟶
      (envelopeObject hp L).thickening.target.dividedPowers.toDividedPowerRing (op ⊤) :=
  DividedPowers.DPMorphism.mk'
    (f := (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom.comp σ)
    (isDPMorphism_of_ideal_eq_bot _ _ _ (SheafOfModules.Submodule.bot_obj _ _))

/-- The map of ambient schemes `Spec D ⟶ U_0 ∩ ⋯ ∩ U_n` of a ring map `σ`. -/
def retractionTargetHom (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object) :
    (envelopeObject hp L).thickening.target ⟶
      ((free S).obj (Over.mk (inter U).ι)).thickening.target :=
  DividedPowerScheme.homOfSectionsDPMorphism (retractionSectionsMap hp L σ)

/-- `retractionTargetHom` on global sections is `σ`. -/
theorem retractionTargetHom_appTop (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object)
    (y : Γ((inter U).toScheme, ⊤)) :
    (retractionTargetHom hp L σ).hom.appTop.hom y =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom (σ y) := by
  have h : (retractionTargetHom hp L σ).hom.appTop =
      CommRingCat.ofHom (retractionSectionsMap hp L σ).toRingHom :=
    DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _
  rw [h]
  rfl

omit [IsAffine S.S.scheme] [S.X.IsSeparated] [∀ k, IsAffine (U k)] in
/-- The structure morphism of the trivial thickening of the intersection, on global sections, is
the algebra map of `Γ(U_0 ∩ ⋯ ∩ U_n)`. -/
theorem free_inter_toBase_appTop (a : Γ(S.S.scheme, ⊤)) :
    ((free S).obj (Over.mk (inter U).ι)).toBase.hom.appTop.hom a =
      algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤) a := by
  have h : ((free S).obj (Over.mk (inter U).ι)).toBase.hom =
      sourceToBase (overSituation S (inter U).ι) :=
    (Category.assoc _ _ _).symm
  rw [h]
  rfl

/-- **The retraction `D_s ⟶ (U_s, U_s, 0)` of a section `σ`**, `U_s = U_0 ∩ ⋯ ∩ U_n`: for an
`A`-algebra map `σ : Γ(U_s) → D` lifting the identification `D / J̄ ≅ Γ(U_s)`, the morphism of
`CRIS(X/S)` which is the identification `Spec (D / J̄) ≅ U_s` on thickened schemes and
`Spec σ : Spec D ⟶ U_s` on ambient schemes. -/
def trivialRetraction (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object)
    (hσA : ∀ a, σ (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤) a) =
      (envelope L).structureMap a)
    (hσ : ∀ y, Ideal.Quotient.mk (envelope L).object.ideal (σ y) = (envelopeEquiv L).symm y) :
    envelopeObject hp L ⟶ (free S).obj (Over.mk (inter U).ι) where
  sourceHom := specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L)
  targetHom := retractionTargetHom hp L σ
  immersion_naturality := by
    refine (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_))).trans
      (Category.comp_id _).symm
    refine (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop _ _) y).trans ?_
    refine (congrArg (envelopeObject hp L).thickening.immersion.appTop.hom
      (retractionTargetHom_appTop hp L σ y)).trans ?_
    exact appTop_specQuotientImmersion_eq (isNilpotent_prime_over S (inter U).ι hp)
      (envelopeThickening hp L) (hσ y)
  base_naturality := by
    refine DividedPowerScheme.Hom.ext
      (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)))
    refine (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop _ _) a).trans ?_
    refine (retractionTargetHom_appTop hp L σ _).trans ?_
    refine (congrArg (fun z ↦ (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      (σ z)) (free_inter_toBase_appTop a)).trans ?_
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      (hσA a)).trans ?_
    exact (envelopeObject_toBase_appTop hp L a).symm
  toX_naturality := (envelopeObject_toX hp L).symm

/-- The retraction on global sections of the ambient schemes is `σ`. -/
theorem trivialRetraction_targetHom_appTop (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object)
    (hσA : ∀ a, σ (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤) a) =
      (envelope L).structureMap a)
    (hσ : ∀ y, Ideal.Quotient.mk (envelope L).object.ideal (σ y) = (envelopeEquiv L).symm y)
    (y : Γ((inter U).toScheme, ⊤)) :
    (trivialRetraction hp L σ hσA hσ).targetHom.hom.appTop.hom y =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom (σ y) :=
  retractionTargetHom_appTop hp L σ y

/-- The retraction, as a morphism of `AffineCris S`. -/
def trivialRetractionHom (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object)
    (hσA : ∀ a, σ (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤) a) =
      (envelope L).structureMap a)
    (hσ : ∀ y, Ideal.Quotient.mk (envelope L).object.ideal (σ y) = (envelopeEquiv L).symm y) :
    envelopeAffine hp L ⟶ (trivialThickeningFunctor S).obj (interAffineOpen U) :=
  ObjectProperty.homMk (ObjectProperty.homMk (trivialRetraction hp L σ hσA hσ))

/-- **The retraction induces a quasi-isomorphism of de Rham complexes** over a base with zero
divided power ideal: given mutually inverse divided power morphisms between the envelope `D` and
a divided power polynomial algebra `Γ(U_s)⟨W⟩` restricting to `σ` on the coefficients, the
transported [Stacks, Tag 07LD] applies to the retraction. -/
theorem quasiIso_map_trivialRetractionHom (hI : (baseSectionsRing S).ideal = ⊥)
    (σ : Γ((inter U).toScheme, ⊤) →+* (envelope L).object)
    (hσA : ∀ a, σ (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤) a) =
      (envelope L).structureMap a)
    (hσ : ∀ y, Ideal.Quotient.mk (envelope L).object.ideal (σ y) = (envelopeEquiv L).symm y)
    {W : Type u}
    (e : DPMorphism (DeRhamPair.polyRing (interDividedPowerRing (U := U) hI) W).dividedPowers
      (envelope L).object.dividedPowers)
    (e' : DPMorphism (envelope L).object.dividedPowers
      (DeRhamPair.polyRing (interDividedPowerRing (U := U) hI) W).dividedPowers)
    (h1 : ∀ c, e.toRingHom (algebraMap (interDividedPowerRing (U := U) hI) _ c) = σ c)
    (h3 : ∀ x, e.toRingHom (e'.toRingHom x) = x) (h4 : ∀ y, e'.toRingHom (e.toRingHom y) = y)
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (hN : N.IsQuasicoherentOnSite) :
    QuasiIso ((bigCrystalDeRhamPresheaf hN).map (trivialRetractionHom hp L σ hσA hσ).op) := by
  set k := trivialRetractionHom hp L σ hσA hσ
  set B₁ := sectionsDPRing S ((trivialThickeningFunctor S).obj (interAffineOpen U)).obj.obj
  let f₁ : (DeRhamPair.polyRing B₁ W : Type u) →+* sectionsDPRing S (envelopeAffine hp L).obj.obj :=
    (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom.comp e.toRingHom
  have hf₁ : ∀ b, f₁ (algebraMap B₁ (DeRhamPair.polyRing B₁ W) b) =
      sectionsDPRingMap k.hom.hom b := fun b ↦ by
    change (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      (e.toRingHom (algebraMap (interDividedPowerRing (U := U) hI) _ b)) = _
    exact (congrArg _ (h1 b)).trans (trivialRetraction_targetHom_appTop hp L σ hσA hσ b).symm
  let e₁ : (DeRhamPair.polyRing B₁ W : Type u) →ₐ[Γ(S.S.scheme, ⊤)]
      sectionsDPRing S (envelopeAffine hp L).obj.obj :=
    { f₁ with
      commutes' := fun a ↦ by
        have h := hf₁ (algebraMap Γ(S.S.scheme, ⊤) B₁ a)
        rw [← IsScalarTower.algebraMap_apply] at h
        exact h.trans ((sectionsDPRingMap k.hom.hom).commutes a) }
  let f₁' : sectionsDPRing S (envelopeAffine hp L).obj.obj →+*
      (DeRhamPair.polyRing B₁ W : Type u) :=
    e'.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom
  have hee' : ∀ c, f₁ (f₁' c) = c := fun c ↦ by
    change (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      (e.toRingHom (e'.toRingHom
        ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom c))) = c
    rw [h3]
    exact ΓSpecIso_inv_hom_apply _ c
  have he'e : ∀ q, f₁' (f₁ q) = q := fun q ↦ by
    change e'.toRingHom ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom (e.toRingHom q))) = q
    rw [DividedPowerScheme.ΓSpecIso_hom_inv_apply]
    exact h4 q
  let e₁' : sectionsDPRing S (envelopeAffine hp L).obj.obj →ₐ[Γ(S.S.scheme, ⊤)]
      (DeRhamPair.polyRing B₁ W : Type u) :=
    { f₁' with
      commutes' := fun a ↦ by
        change f₁' _ = _
        rw [← e₁.commutes a]
        exact he'e _ }
  have he : IsDPMorphism (DeRhamPair.polyRing B₁ W).dividedPowers
      (sectionsDPRing S (envelopeAffine hp L).obj.obj).dividedPowers e₁.toRingHom := by
    exact isDPMorphism_polyRing_source_of_eq_bot (map_baseIdeal_inter_eq_bot hI)
      (SheafOfModules.Submodule.bot_obj _ _) _ _ W _ _
      ((DividedPowerScheme.specSectionsRingIso (envelope L).object).hom.comp e).isDPMorphism
  have he' : IsDPMorphism (sectionsDPRing S (envelopeAffine hp L).obj.obj).dividedPowers
      (DeRhamPair.polyRing B₁ W).dividedPowers e₁'.toRingHom := by
    exact isDPMorphism_polyRing_target_of_eq_bot (map_baseIdeal_inter_eq_bot hI)
      (SheafOfModules.Submodule.bot_obj _ _) _ _ W _ _
      (e'.comp (DividedPowerScheme.specSectionsRingIso (envelope L).object).inv).isDPMorphism
  exact quasiIso_crystalDeRhamPresheaf_map (isQuasicoherentOnSite_restrictSheafOfModules hN) k W
    e₁ hf₁ e₁' hee' he'e he he'

end Retraction

/-! ### The rows over a base with zero divided power ideal -/

section Rows

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

attribute [local instance] interAlgebra

/-- **The envelope object of a tuple is a product of the `D_{x a}` in `AffineCris S`**: it is one
in `Cris(X/S)` (`CechEnvelope.isLimitCrisFan`), and `AffineCris S` is a full subcategory. -/
def isLimitEnvelopeAffineFan {n : ℕ} (x : Fin (n + 1) → ι) :
    IsLimit (Fan.mk (envelopeAffine hp (fun a ↦ L (x a)))
      (fun a ↦ ObjectProperty.homMk (ObjectProperty.homMk (proj hp (fun a ↦ L (x a)) a))) :
        Fan fun a ↦ affineObject hp L (x a)) :=
  Fan.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk
      (Fan.IsLimit.lift (isLimitCrisFan hp L x) fun a ↦ (s.proj a).hom))
    (fun s a ↦ by
      ext1
      exact Fan.IsLimit.fac (isLimitCrisFan hp L x) _ a)
    (fun s m hm ↦ by
      ext1
      refine Fan.IsLimit.hom_ext (isLimitCrisFan hp L x) _ _ fun a ↦ ?_
      exact (congrArg (fun g ↦ g.hom) (hm a)).trans
        (Fan.IsLimit.fac (isLimitCrisFan hp L x) (fun a ↦ (s.proj a).hom) a).symm)

omit [IsAffine S.S.scheme] in
/-- The intersection `U_{x 0} ∩ ⋯ ∩ U_{x n}`, as an affine open, is the product of the `U_{x a}`
among the affine opens. -/
def interAffineOpenIso {n : ℕ} (x : Fin (n + 1) → ι) :
    interAffineOpen (fun a ↦ U (x a)) ≅ Stacks.CechSite.FinalCover.inter (chartOpen U) x where
  hom := ObjectProperty.homMk (homOfLE (AffineOpens.piObj_obj fun a ↦ chartOpen U (x a)).ge)
  inv := ObjectProperty.homMk (homOfLE (AffineOpens.piObj_obj fun a ↦ chartOpen U (x a)).le)
  hom_inv_id := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
  inv_hom_id := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)

/-- **On the factor indexed by a tuple `x`, the comparison of de Rham complexes along
`(U_x, U_x, 0) ⟶ D_x` is a quasi-isomorphism**, over a base with zero divided power ideal and
for smooth lifts with étale coordinates.  The map `(U_x, U_x, 0) ⟶ D_x` (whichever it is: there
is only one) has the retraction `CechEnvelope.trivialRetraction` of the section `σ` of
`CechEnvelope.exists_dpPolynomial_equiv_envelope_of_ideal_eq_bot`, which induces a
quasi-isomorphism (`CechEnvelope.quasiIso_map_trivialRetractionHom`); the composite
`(U_x, U_x, 0) ⟶ D_x ⟶ (U_x, U_x, 0)` is the identity, so the claim is two out of three. -/
theorem quasiIso_map_interComparison (hI : (baseSectionsRing S).ideal = ⊥) {d : ι → ℕ}
    (t : ∀ i, Fin (d i) → (L i).ring)
    (ht : ∀ i, (MvPolynomial.aeval (R := baseSectionsRing S) (t i)).toRingHom.Etale)
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (hN : N.IsQuasicoherentOnSite)
    (c : ∀ i, (trivialThickeningFunctor S).obj (chartOpen U i) ⟶ affineObject hp L i)
    {n : ℕ} (x : Fin (n + 1) → ι) :
    QuasiIso ((bigCrystalDeRhamPresheaf hN).map
      (interComparison (trivialThickeningFunctor S) c x).op) := by
  let : Algebra (baseSectionsRing S) (envelope fun a ↦ L (x a)).object :=
    (envelope fun a ↦ L (x a)).structureMap.toRingHom.toAlgebra
  obtain ⟨σ, hσ, -, e, e', h1, -, h3, h4⟩ :=
    exists_dpPolynomial_equiv_envelope_of_ideal_eq_bot hI (fun a ↦ L (x a)) S.prime.out hp
      (fun a ↦ t (x a)) (fun a ↦ ht (x a))
  have hr' := quasiIso_map_trivialRetractionHom hp (fun a ↦ L (x a)) hI σ.toRingHom σ.commutes
    hσ e e' h1 h3 h4 hN
  let α := (isLimitInterFan (affineObject hp L) x).conePointUniqueUpToIso
    (isLimitEnvelopeAffineFan hp L x)
  let r := α.hom ≫ trivialRetractionHom hp (fun a ↦ L (x a)) σ.toRingHom σ.commutes hσ ≫
    (trivialThickeningFunctor S).map (interAffineOpenIso x).hom
  have hr : QuasiIso ((bigCrystalDeRhamPresheaf hN).map r.op) := by
    simp only [r, op_comp, Functor.map_comp]
    infer_instance
  have : QuasiIso ((bigCrystalDeRhamPresheaf hN).map r.op ≫ (bigCrystalDeRhamPresheaf hN).map
      (interComparison (trivialThickeningFunctor S) c x).op) := by
    rw [← Functor.map_comp, ← op_comp,
      trivialThickeningFunctor_hom_ext (interComparison (trivialThickeningFunctor S) c x ≫ r)
        (𝟙 _), op_id, CategoryTheory.Functor.map_id]
    infer_instance
  exact quasiIso_of_comp_left ((bigCrystalDeRhamPresheaf hN).map r.op) _

/-- **The comparison `B ⟶ C` of Čech–de Rham double complexes is a quasi-isomorphism on every
row**, over a base with zero divided power ideal, for finitely many affine opens `U_i` of `X`
with smooth lifts carrying étale coordinates. -/
theorem quasiIso_rowMap_trivialRowHom [Finite ι] (hI : (baseSectionsRing S).ideal = ⊥)
    {d : ι → ℕ} (t : ∀ i, Fin (d i) → (L i).ring)
    (ht : ∀ i, (MvPolynomial.aeval (R := baseSectionsRing S) (t i)).toRingHom.Etale)
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (b : ℕ) : QuasiIso (rowMap (trivialRowHom hp L N hN) b) :=
  quasiIso_rowMap_doubleComplexComparison (trivialThickeningFunctor S) (trivialChartHom hp L)
    (bigCrystalDeRhamPresheaf hN) (fun _ x ↦ quasiIso_map_interComparison hp L hI t ht hN _ x) b

/-- **The Čech–de Rham double complexes of the cover by the `D_i` and of the cover by the trivial
thickenings `(U_i, U_i, 0)` have isomorphic total cohomology**, over a base with zero divided
power ideal, for finitely many affine opens `U_i` of `X` with smooth lifts carrying étale
coordinates: the comparison `CechEnvelope.trivialRowHom` is a quasi-isomorphism on every row. -/
def trivialRowsHomologyIso [Finite ι] (hI : (baseSectionsRing S).ideal = ⊥)
    {d : ι → ℕ} (t : ∀ i, Fin (d i) → (L i).ring)
    (ht : ∀ i, (MvPolynomial.aeval (R := baseSectionsRing S) (t i)).toRingHom.Etale)
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (n : ℤ) :
    (((Crystalline.CosimplicialDoubleComplex.functor _).obj
        (cechDeRhamDoubleComplex hp L N hN)).total (ComplexShape.up ℤ)).homology n ≅
      (((Crystalline.CosimplicialDoubleComplex.functor _).obj
        (trivialCechDeRhamDoubleComplex U N hN)).total (ComplexShape.up ℤ)).homology n :=
  totalHomologyIsoOfRows (trivialRowHom hp L N hN)
    (quasiIso_rowMap_trivialRowHom hp L hI t ht N hN) n

end Rows

end Crystalline.GlobalCrystallineSituation.CechEnvelope
