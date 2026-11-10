module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcHomGlueAffine
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparisonRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcGluing

/-!
# Fpqc descent of morphisms of quasi-coherent modules on algebraic spaces

This file proves the gluing half of the full-faithfulness clause of Stacks 04W8 in the form the
relative Hom functor of Stacks 08JT consumes,
`AlgebraicGeometry.Space.GluesModuleHomAlongFpqcCovering`:
given an fpqc covering `(c i : Z i ⟶ W)` of algebraic spaces, a morphism `w : W ⟶ X` and two
`𝒪_X`-modules whose inverse images along `w` are quasi-coherent, a family of homomorphisms of
the inverse images along the composites which agrees on the overlaps comes from a unique
homomorphism over `W`.

The proof is the strategy of the source: reduce to the case of schemes étale locally on `W`.
Over an affine object of the site mapping to `W` the covering is refined by a finite affine fpqc
covering (the definition of Stacks 03MQ), where the affine case of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FpqcHomGlueAffine.lean` applies; the
local homomorphisms are then glued along an étale covering by affine schemes, which is descent
of morphisms along an étale covering (Stacks 04W6).

## Main definitions

* `AlgebraicGeometry.Space.IsCompatibleAt`: a homomorphism over a space mapping to `W` is
  compatible with the family when all its restrictions agree with the restrictions of the
  members of the family.

## Main results

* `AlgebraicGeometry.Space.IsCompatibleAt.eq`: compatible homomorphisms are unique (the
  faithfulness half of Stacks 04W8).
* `AlgebraicGeometry.Space.IsCompatibleAt.of_isFpqcCovering`: compatibility descends along an
  fpqc covering.
* `AlgebraicGeometry.Space.exists_isCompatibleAt`: compatible homomorphisms exist over every
  algebraic space mapping to `W`.
* `AlgebraicGeometry.Space.gluesModuleHomAlongFpqcCovering`:
  **`AlgebraicGeometry.Space.GluesModuleHomAlongFpqcCovering` holds.**

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (reprSpaceMap)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport along the composition comparison commutes with restriction**, for arbitrary
morphisms (the form of `AlgebraicGeometry.Space.transportHom_modulePullbackTriangle` without
algebraic spaces over `W`). -/
theorem transportHom_restrictPullbackHom {X W Z Z' : AlgebraicSpaces B S hS} (w : W ⟶ X)
    (F G : Modules.{u, u} B S hS X.1 X.2) (zh : Z ⟶ W) (z'h : Z' ⟶ W) (m : Z' ⟶ Z)
    (hm : m ≫ zh = z'h) (h' : m ≫ zh ≫ w = z'h ≫ w)
    (α : (modulePullback B S hS zh).obj ((modulePullback B S hS w).obj F) ⟶
      (modulePullback B S hS zh).obj ((modulePullback B S hS w).obj G)) :
    Functor.transportHom (modulePullbackTriangle B S hS (rfl : z'h ≫ w = z'h ≫ w))
        (Functor.conjHom (modulePullbackTriangle B S hS hm) α) =
      restrictPullbackHom m h'
        (Functor.transportHom (modulePullbackTriangle B S hS (rfl : zh ≫ w = zh ≫ w)) α) :=
  transportHom_modulePullbackTriangle (modulePushforwardCoherence B S hS) w F G
    (Z := Over.mk zh) (Z' := Over.mk z'h) (Over.homMk m hm) α

/-- Transporting a conjugated lift `(transportHomEquiv _ F G).symm ψ` back gives the restriction
of `ψ`. -/
private theorem transportHom_conjHom_transportHomEquiv_symm {X W Z Z' : AlgebraicSpaces B S hS}
    (w : W ⟶ X) (F G : Modules.{u, u} B S hS X.1 X.2) (zh : Z ⟶ W) (z'h : Z' ⟶ W) (m : Z' ⟶ Z)
    (hm : m ≫ zh = z'h) (h' : m ≫ zh ≫ w = z'h ≫ w)
    (ψ : (modulePullback B S hS (zh ≫ w)).obj F ⟶ (modulePullback B S hS (zh ≫ w)).obj G) :
    Functor.transportHom (modulePullbackTriangle B S hS (rfl : z'h ≫ w = z'h ≫ w))
        (Functor.conjHom (modulePullbackTriangle B S hS hm)
          ((Functor.transportHomEquiv
            (modulePullbackTriangle B S hS (rfl : zh ≫ w = zh ≫ w)) F G).symm ψ)) =
      restrictPullbackHom m h' ψ :=
  (transportHom_restrictPullbackHom B S hS w F G zh z'h m hm h' _).trans
    (congrArg _ ((Functor.transportHomEquiv
      (modulePullbackTriangle B S hS (rfl : zh ≫ w = zh ≫ w)) F G).apply_symm_apply ψ))

/-- **The affine represented case, for modules pulled back from a further algebraic space.** -/
theorem exists_restrict_eq_of_reprFamily {X : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS X.1 X.2} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (w : representedAlgebraicSpace B S hS T ⟶ X)
    (hF : ((modulePullback B S hS w).obj F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS w).obj G).IsQuasicoherentOnSite)
    {ι : Type*} [Finite ι] {U : ι → BigFppfOver B S hS}
    (hU : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (U j))) (g : ∀ j, U j ⟶ T)
    (hff : letI := reprFamilyAlgebra B S hS g
      Module.FaithfullyFlat (reprRing B S hS T) (∀ j, reprRing B S hS (U j)))
    (P : ι → ι → BigFppfOver B S hS)
    (hP : ∀ j k, IsAffine ((BigFppfOver.toScheme B S hS).obj (P j k)))
    (p : ∀ j k, P j k ⟶ U j) (q : ∀ j k, P j k ⟶ U k)
    (hpq : ∀ j k, q j k ≫ g k = p j k ≫ g j)
    (hpush : ∀ j k, letI := reprAlgebra B S hS (g j); letI := reprAlgebra B S hS (g k)
      letI := reprAlgebra B S hS (p j k ≫ g j)
      Function.Bijective (Algebra.TensorProduct.productMap
        (reprRestrictAlgHom B S hS (p j k) (g j) rfl)
        (reprRestrictAlgHom B S hS (q j k) (g k) (hpq j k))))
    (α : ∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j) ≫ w)).obj F ⟶
      (modulePullback B S hS (reprSpaceMap B S hS (g j) ≫ w)).obj G)
    (hα : ∀ j k, restrictPullbackHom (reprSpaceMap B S hS (p j k))
        (by rw [← Category.assoc, reprSpaceMap_comp_eq B S hS (p j k) (g j) rfl] :
          reprSpaceMap B S hS (p j k) ≫ reprSpaceMap B S hS (g j) ≫ w =
            reprSpaceMap B S hS (p j k ≫ g j) ≫ w) (α j) =
      restrictPullbackHom (reprSpaceMap B S hS (q j k))
        (by rw [← Category.assoc, reprSpaceMap_comp_eq B S hS (q j k) (g k) (hpq j k)] :
          reprSpaceMap B S hS (q j k) ≫ reprSpaceMap B S hS (g k) ≫ w =
            reprSpaceMap B S hS (p j k ≫ g j) ≫ w) (α k)) :
    ∃ β : (modulePullback B S hS w).obj F ⟶ (modulePullback B S hS w).obj G,
      ∀ j, restrictPullbackHom (reprSpaceMap B S hS (g j)) rfl β = α j := by
  let e : ∀ j, _ := fun j => Functor.transportHomEquiv
    (modulePullbackTriangle B S hS (rfl : reprSpaceMap B S hS (g j) ≫ w = _)) F G
  obtain ⟨β, hβ⟩ := exists_hom_of_reprFamily B S hS hT hU g hff P hP p q hpq hpush hF hG
    (fun j => (e j).symm (α j)) fun j k => by
      refine (Functor.transportHomEquiv (modulePullbackTriangle B S hS
        (rfl : reprSpaceMap B S hS (p j k ≫ g j) ≫ w = _)) F G).injective ?_
      exact (transportHom_conjHom_transportHomEquiv_symm B S hS w F G _ _ _
        (reprSpaceMap_comp_eq B S hS (p j k) (g j) rfl) _ (α j)).trans
        ((hα j k).trans (transportHom_conjHom_transportHomEquiv_symm B S hS w F G _ _ _
          (reprSpaceMap_comp_eq B S hS (q j k) (g k) (hpq j k)) _ (α k)).symm)
  exact ⟨β, fun j => (e j).eq_symm_apply.1 (hβ j)⟩

/-- A conjugation identity in an arbitrary category. -/
theorem conj_iso_aux {C : Type*} [Category C] {KM KN AM AN BM BN : C}
    (tAM : KM ≅ AM) (tAN : KN ≅ AN) (tBM : KM ≅ BM) (tBN : KN ≅ BN) (x : AM ⟶ AN)
    (y : BM ⟶ BN) (hw : tAM.hom ≫ x ≫ tAN.inv = tBM.hom ≫ y ≫ tBN.inv) :
    x ≫ (tAN.symm ≪≫ tBN).hom = (tAM.symm ≪≫ tBM).hom ≫ y := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  have hw2 := (Iso.eq_inv_comp tAM).2 hw
  rw [← Category.assoc x, hw2]
  simp

/-- The canonical comparison is the composite of two composition comparisons. -/
theorem canonicalComparisonIso_eq_triangle {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) :
    QuasiCoherentDescent.canonicalComparisonIso B S hS a b fi fj h =
      (modulePullbackTriangle B S hS (rfl : a ≫ fi = a ≫ fi)).symm ≪≫
        modulePullbackTriangle B S hS h.symm := by
  rw [modulePullbackTriangle_rfl, modulePullbackTriangle_eq]
  simp [QuasiCoherentDescent.canonicalComparisonIso]

/-- **Agreement of restrictions is the pairwise condition of a morphism of descent data.** -/
theorem canonicalComparison_eq_of_conjHom_eq {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    {M N : Modules.{u, u} B S hS A.1 A.2}
    (wi : (modulePullback B S hS fi).obj M ⟶ (modulePullback B S hS fi).obj N)
    (wj : (modulePullback B S hS fj).obj M ⟶ (modulePullback B S hS fj).obj N)
    (hw : Functor.conjHom (modulePullbackTriangle B S hS (rfl : a ≫ fi = a ≫ fi)) wi =
      Functor.conjHom (modulePullbackTriangle B S hS h.symm) wj) :
    (modulePullback B S hS a).map wi ≫
        (QuasiCoherentDescent.canonicalComparison a b fi fj h N).hom =
      (QuasiCoherentDescent.canonicalComparison a b fi fj h M).hom ≫
        (modulePullback B S hS b).map wj := by
  rw [← QuasiCoherentDescent.canonicalComparisonIso_app,
    ← QuasiCoherentDescent.canonicalComparisonIso_app, canonicalComparisonIso_eq_triangle]
  exact conj_iso_aux ((modulePullbackTriangle B S hS (rfl : a ≫ fi = a ≫ fi)).app M)
    ((modulePullbackTriangle B S hS (rfl : a ≫ fi = a ≫ fi)).app N)
    ((modulePullbackTriangle B S hS h.symm).app M) ((modulePullbackTriangle B S hS h.symm).app N)
    _ _ hw

/-! ### Compatibility with a family of local homomorphisms -/

section Compatible

variable {X W : AlgebraicSpaces B S hS} (w : W ⟶ X) {I : Type v}
  {Zi : I → AlgebraicSpaces B S hS} (c : ∀ i, Zi i ⟶ W) (q : ∀ i, Zi i ⟶ X)
  (hq : ∀ i, c i ≫ w = q i) {F G : Modules.{u, u} B S hS X.1 X.2}
  (α : ∀ i, (modulePullback B S hS (q i)).obj F ⟶ (modulePullback B S hS (q i)).obj G)

/-- A homomorphism `δ : y^*F ⟶ y^*G`, for `y = y₀ ≫ w`, is *compatible* with the family `α` when
its restriction along any `t` agrees with the restriction of `α i` along any `s` with
`s ≫ c i = t ≫ y₀`. -/
def IsCompatibleAt {Y : AlgebraicSpaces B S hS} (y₀ : Y ⟶ W) (y : Y ⟶ X) (_hy : y₀ ≫ w = y)
    (δ : (modulePullback B S hS y).obj F ⟶ (modulePullback B S hS y).obj G) : Prop :=
  ∀ (Y' : AlgebraicSpaces B S hS) (i : I) (s : Y' ⟶ Zi i) (t : Y' ⟶ Y) (r : Y' ⟶ X)
    (ht : t ≫ y = r) (hs : s ≫ q i = r), s ≫ c i = t ≫ y₀ →
    restrictPullbackHom t ht δ = restrictPullbackHom s hs (α i)

variable {w c q hq α}

/-- **Each member of a family agreeing on the overlaps is compatible with the family.** -/
theorem isCompatibleAt_self (hα : RestrictionsAgree w c q hq α) (i : I) :
    IsCompatibleAt B S hS w c q α (c i) (q i) (hq i) (α i) := by
  intro Y' j s t r ht hs hst
  let l : Y' ⟶ overlapSpace c i j :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (c i) (c j)).lift t s hst.symm
  have hl1 : l ≫ overlapFst c i j = t :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (c i) (c j)).lift_fst _ _ _
  have hl2 : l ≫ overlapSnd c i j = s :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (c i) (c j)).lift_snd _ _ _
  have hb : l ≫ overlapFst c i j ≫ q i = r := by rw [← Category.assoc, hl1, ht]
  have e1 := restrictPullbackHom_comp (overlapFst c i j) rfl l hb
    (by rw [hl1, ht]) (α i)
  have e2 := restrictPullbackHom_comp (overlapSnd c i j) (overlapSnd_comp_eq w c q hq i j) l hb
    (by rw [Category.assoc, overlapSnd_comp_eq w c q hq i j, hb]) (α j)
  refine (restrictPullbackHom_congr hl1.symm ht (by rw [hl1, ht]) (α i)).trans ?_
  refine e1.trans ?_
  refine (congrArg (restrictPullbackHom l hb) (hα i j)).trans ?_
  refine e2.symm.trans ?_
  exact restrictPullbackHom_congr hl2 _ _ (α j)

/-- **Restrictions of compatible homomorphisms are compatible.** -/
theorem IsCompatibleAt.restrict {Y Y₁ : AlgebraicSpaces B S hS} {y₀ : Y ⟶ W} {y : Y ⟶ X}
    {hy : y₀ ≫ w = y} {δ : (modulePullback B S hS y).obj F ⟶ (modulePullback B S hS y).obj G}
    (hδ : IsCompatibleAt B S hS w c q α y₀ y hy δ) (a : Y₁ ⟶ Y) {y₁₀ : Y₁ ⟶ W}
    (ha₀ : a ≫ y₀ = y₁₀) {y₁ : Y₁ ⟶ X} (hy₁ : y₁₀ ≫ w = y₁) (ha : a ≫ y = y₁) :
    IsCompatibleAt B S hS w c q α y₁₀ y₁ hy₁ (restrictPullbackHom a ha δ) := by
  intro Y' i s t r ht hs hst
  have hst' : s ≫ c i = (t ≫ a) ≫ y₀ := by rw [hst, ← ha₀, Category.assoc]
  have hta : (t ≫ a) ≫ y = r := by rw [Category.assoc, ha, ht]
  exact (restrictPullbackHom_comp a ha t ht hta δ).symm.trans (hδ Y' i s (t ≫ a) r hta hs hst')

include hq in
/-- **Compatible homomorphisms are unique**, for an fpqc covering `c`. -/
theorem IsCompatibleAt.eq (hc : IsFpqcCovering B S hS fun i => (c i).hom)
    {Y : AlgebraicSpaces B S hS} {y₀ : Y ⟶ W} {y : Y ⟶ X} {hy : y₀ ≫ w = y}
    {δ δ' : (modulePullback B S hS y).obj F ⟶ (modulePullback B S hS y).obj G}
    (hδ : IsCompatibleAt B S hS w c q α y₀ y hy δ)
    (hδ' : IsCompatibleAt B S hS w c q α y₀ y hy δ') : δ = δ' := by
  have hcov := isFpqcCovering_pullback B S hS c y₀ hc
  refine eq_of_restrictPullbackHom_eq_of_isFpqcCovering
    (QuasiCoherentDescent.reprFpqcHomInjective B S hS)
    (fun i => fiberSnd (c i) y₀) (fun i => rfl) hcov δ δ' fun i => ?_
  have hsq : fiberFst (c i) y₀ ≫ c i = fiberSnd (c i) y₀ ≫ y₀ :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (c i) y₀).w
  have hs : fiberFst (c i) y₀ ≫ q i = fiberSnd (c i) y₀ ≫ y := by
    rw [← hq i, ← hy, ← Category.assoc, hsq, Category.assoc]
  exact (hδ _ i _ _ _ rfl hs hsq).trans (hδ' _ i _ _ _ rfl hs hsq).symm

/-- **Compatibility descends along an fpqc covering of the source.** -/
theorem IsCompatibleAt.of_isFpqcCovering {J : Type*} {Y : AlgebraicSpaces B S hS}
    {Yj : J → AlgebraicSpaces B S hS} (d : ∀ j, Yj j ⟶ Y)
    (hd : IsFpqcCovering B S hS fun j => (d j).hom) {y₀ : Y ⟶ W} {y : Y ⟶ X}
    {hy : y₀ ≫ w = y} {δ : (modulePullback B S hS y).obj F ⟶ (modulePullback B S hS y).obj G}
    (h : ∀ j, IsCompatibleAt B S hS w c q α (d j ≫ y₀) (d j ≫ y)
      (by rw [Category.assoc, hy]) (restrictPullbackHom (d j) rfl δ)) :
    IsCompatibleAt B S hS w c q α y₀ y hy δ := by
  intro Y' i s t r ht hs hst
  have hcov := isFpqcCovering_pullback B S hS d t hd
  refine eq_of_restrictPullbackHom_eq_of_isFpqcCovering
    (QuasiCoherentDescent.reprFpqcHomInjective B S hS)
    (fun j => fiberSnd (d j) t) (fun j => rfl) hcov _ _ fun j => ?_
  have hsq : fiberFst (d j) t ≫ d j = fiberSnd (d j) t ≫ t :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (d j) t).w
  have h1 : (fiberSnd (d j) t ≫ t) ≫ y = fiberSnd (d j) t ≫ r := by rw [Category.assoc, ht]
  have h2 : (fiberFst (d j) t ≫ d j) ≫ y = fiberSnd (d j) t ≫ r := by rw [hsq, h1]
  have h3 : fiberFst (d j) t ≫ d j ≫ y = fiberSnd (d j) t ≫ r := by rw [← Category.assoc, h2]
  have h4 : (fiberSnd (d j) t ≫ s) ≫ q i = fiberSnd (d j) t ≫ r := by rw [Category.assoc, hs]
  have hst' : (fiberSnd (d j) t ≫ s) ≫ c i = fiberFst (d j) t ≫ d j ≫ y₀ := by
    rw [Category.assoc, hst, ← Category.assoc, ← hsq, Category.assoc]
  refine (restrictPullbackHom_comp t ht (fiberSnd (d j) t) rfl h1 δ).symm.trans ?_
  refine (restrictPullbackHom_congr hsq.symm h1 h2 δ).trans ?_
  refine (restrictPullbackHom_comp (d j) rfl (fiberFst (d j) t) h3 h2 δ).trans ?_
  refine (h j _ i _ _ _ h3 h4 hst').trans ?_
  exact restrictPullbackHom_comp s hs (fiberSnd (d j) t) rfl h4 (α i)

include hq in
/-- **A compatible homomorphism exists over an affine represented algebraic space.** -/
theorem exists_isCompatibleAt_repr (hc : IsFpqcCovering B S hS fun i => (c i).hom)
    (hα : ∀ i, IsCompatibleAt B S hS w c q α (c i) (q i) (hq i) (α i))
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (b : representedAlgebraicSpace B S hS T ⟶ W) (y : representedAlgebraicSpace B S hS T ⟶ X)
    (hy : b ≫ w = y)
    (hF : ((modulePullback B S hS y).obj F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS y).obj G).IsQuasicoherentOnSite) :
    ∃ δ, IsCompatibleAt B S hS w c q α b y hy δ := by
  classical
  subst hy
  obtain ⟨E, hfin, hmem, hlift⟩ := hc.2 ⟨T, hT⟩ b.hom
  choose i a ha using hlift
  let g : ∀ j, (BigAffineFppf.inclusion B S hS).obj (E.X j) ⟶ T := fun j =>
    (BigAffineFppf.inclusion B S hS).map (E.f j)
  have hmem' : Presieve.ofArrows
      (fun j => (BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.X j)))
      (fun j => (BigFppfOver.toScheme B S hS).map (g j)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj T) := by
    have := hmem
    rw [Presieve.map_ofArrows] at this
    exact this
  have hprec := (Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hmem')
  have hU : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (E.X j))) := fun j => (E.X j).property
  let a' : ∀ j, representedAlgebraicSpace B S hS ((BigAffineFppf.inclusion B S hS).obj (E.X j)) ⟶
      Zi (i j) := fun j => ObjectProperty.homMk (a j)
  have ha' : ∀ j, a' j ≫ c (i j) = reprSpaceMap B S hS (g j) ≫ b := fun j =>
    ObjectProperty.hom_ext _ (ha j)
  have hqa : ∀ j, a' j ≫ q (i j) = reprSpaceMap B S hS (g j) ≫ b ≫ w := fun j => by
    rw [← hq, ← Category.assoc, ha', Category.assoc]
  let α' : ∀ j, _ := fun j => restrictPullbackHom (a' j) (hqa j) (α (i j))
  have hα' : ∀ j, IsCompatibleAt B S hS w c q α (reprSpaceMap B S hS (g j) ≫ b)
      (reprSpaceMap B S hS (g j) ≫ b ≫ w) (by rw [Category.assoc]) (α' j) := fun j =>
    (hα (i j)).restrict B S hS (a' j) (ha' j) _ (hqa j)
  have : Finite E.I₀ := hfin
  have hff := faithfullyFlat_reprFamily B S hS hT hU g hprec.2 fun x => by
    obtain ⟨j, y, hy⟩ := hprec.1 x
    exact ⟨j, y, hy⟩
  obtain ⟨β, hβ⟩ := exists_restrict_eq_of_reprFamily B S hS hT (b ≫ w) hF hG hU g hff
    (fun j k => pullback (g j) (g k))
    (fun j k => isAffine_pullback_bigFppfOver B S hS (g j) (g k) hT (hU j) (hU k))
    (fun j k => pullback.fst (g j) (g k)) (fun j k => pullback.snd (g j) (g k))
    (fun j k => pullback.condition.symm)
    (fun j k => bijective_productMap_reprRestrict B S hS (g j) (g k) hT (hU j) (hU k))
    α' fun j k => by
      refine IsCompatibleAt.eq B S hS (hq := hq) (α := α) hc
        (y₀ := reprSpaceMap B S hS (pullback.fst (g j) (g k) ≫ g j) ≫ b)
        (hy := by rw [Category.assoc]) ?_ ?_
      · exact (hα' j).restrict B S hS (reprSpaceMap B S hS (pullback.fst (g j) (g k)))
          (by rw [← Category.assoc, reprSpaceMap_comp_eq B S hS _ _ rfl])
          (by rw [Category.assoc]) _
      · exact (hα' k).restrict B S hS (reprSpaceMap B S hS (pullback.snd (g j) (g k)))
          (by rw [← Category.assoc, reprSpaceMap_comp_eq B S hS _ _ pullback.condition.symm])
          (by rw [Category.assoc]) _
  refine ⟨β, IsCompatibleAt.of_isFpqcCovering B S hS (fun j => reprSpaceMap B S hS (g j))
    (represented_fpqc_family B S hS E.I₀ _ g hmem') fun j => ?_⟩
  rw [hβ j]
  exact hα' j

include hq in
/-- **A compatible homomorphism exists over every algebraic space mapping to `W`.** -/
theorem exists_isCompatibleAt (hc : IsFpqcCovering B S hS fun i => (c i).hom)
    (hα : ∀ i, IsCompatibleAt B S hS w c q α (c i) (q i) (hq i) (α i))
    {Y : AlgebraicSpaces B S hS} (y₀ : Y ⟶ W) (y : Y ⟶ X) (hy : y₀ ≫ w = y)
    (hF : ((modulePullback B S hS y).obj F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS y).obj G).IsQuasicoherentOnSite) :
    ∃ δ, IsCompatibleAt B S hS w c q α y₀ y hy δ := by
  classical
  obtain ⟨Yx, bx, hYaff, hbet, -, hcov⟩ := exists_isEtaleCovering_affine B S hS Y.1 Y.2
  let b' : ∀ x, representedAlgebraicSpace B S hS (Yx x) ⟶ Y := fun x => ObjectProperty.homMk (bx x)
  have hqc : ∀ x (M : Modules.{u, u} B S hS X.1 X.2),
      ((modulePullback B S hS y).obj M).IsQuasicoherentOnSite →
      ((modulePullback B S hS ((b' x ≫ y₀) ≫ w)).obj M).IsQuasicoherentOnSite := by
    intro x M hM
    have h1 := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (b' x) _ hM
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePullbackTriangle B S hS (by rw [Category.assoc, hy] :
        b' x ≫ y = (b' x ≫ y₀) ≫ w)).app M).symm h1
  have hy' : ∀ x, (b' x ≫ y₀) ≫ w = b' x ≫ y := fun x => by rw [Category.assoc, hy]
  have hqc' : ∀ x (M : Modules.{u, u} B S hS X.1 X.2),
      ((modulePullback B S hS y).obj M).IsQuasicoherentOnSite →
      ((modulePullback B S hS (b' x ≫ y)).obj M).IsQuasicoherentOnSite := fun x M hM => by
    rw [← hy' x]; exact hqc x M hM
  choose ψ hψ using fun x => exists_isCompatibleAt_repr B S hS (hq := hq) hc hα (hYaff x)
    (b' x ≫ y₀) (b' x ≫ y) (hy' x) (hqc' x F hF) (hqc' x G hG)
  let e : ∀ x, _ := fun x => Functor.transportHomEquiv
    (modulePullbackTriangle B S hS (rfl : b' x ≫ y = b' x ≫ y)) F G
  let wx : ∀ x, (modulePullback B S hS (b' x)).obj ((modulePullback B S hS y).obj F) ⟶
      (modulePullback B S hS (b' x)).obj ((modulePullback B S hS y).obj G) :=
    fun x => (e x).symm (ψ x)
  have hwx : ∀ x, Functor.transportHom (modulePullbackTriangle B S hS
      (rfl : b' x ≫ y = b' x ≫ y)) (wx x) = ψ x := fun x => (e x).apply_symm_apply (ψ x)
  have hpair : QuasiCoherentDescent.IsPairwiseCompatible B S hS
      (fun x => representedAlgebraicSpace B S hS (Yx x)) b' wx := by
    intro x x'
    let a := QuasiCoherentDescent.pairFst B S hS
      (fun x => representedAlgebraicSpace B S hS (Yx x)) b' x x'
    let a' := QuasiCoherentDescent.pairSnd B S hS
      (fun x => representedAlgebraicSpace B S hS (Yx x)) b' x x'
    refine canonicalComparison_eq_of_conjHom_eq B S hS _ _ _ _ _ _ _ ?_
    have hc' : a ≫ b' x = a' ≫ b' x' := QuasiCoherentDescent.pair_condition B S hS _ b' x x'
    let er := Functor.transportHomEquiv (modulePullbackTriangle B S hS
      (rfl : (a ≫ b' x) ≫ y = (a ≫ b' x) ≫ y)) F G
    have inj : Function.Injective (Functor.transportHom (modulePullbackTriangle B S hS
        (rfl : (a ≫ b' x) ≫ y = (a ≫ b' x) ≫ y)) (M := F) (N := G)) := er.injective
    refine inj ?_
    refine (transportHom_conjHom_transportHomEquiv_symm B S hS y F G (b' x) _ a rfl
        (Category.assoc _ _ _).symm (ψ x)).trans
      (Eq.trans ?_ (transportHom_conjHom_transportHomEquiv_symm B S hS y F G (b' x') _ a'
        hc'.symm (by rw [← Category.assoc, hc'.symm]) (ψ x')).symm)
    refine IsCompatibleAt.eq B S hS (hq := hq) (α := α) hc (y₀ := (a ≫ b' x) ≫ y₀)
      (hy := by rw [Category.assoc, Category.assoc, hy, Category.assoc]) ?_ ?_
    · exact (hψ x).restrict B S hS a (by rw [Category.assoc]) _ _
    · exact (hψ x').restrict B S hS a' (by rw [← Category.assoc, hc']) _ _
  obtain ⟨β, hβ⟩ := QuasiCoherentDescent.exists_modulePullback_map_eq B S hS
    (fun x => representedAlgebraicSpace B S hS (Yx x)) b' hbet
    (QuasiCoherentDescent.pairEtaleRestrictionComp_of_representable B S hS _ b' hbet
      fun x => relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 (bx x)) hcov wx hpair
  refine ⟨β, IsCompatibleAt.of_isFpqcCovering B S hS b'
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov) fun x => ?_⟩
  have h1 : restrictPullbackHom (b' x) rfl β = ψ x := by
    refine Eq.trans ?_ (hwx x)
    change Functor.transportHom (modulePullbackTriangle B S hS (rfl : b' x ≫ y = b' x ≫ y))
      ((modulePullback B S hS (b' x)).map β) = _
    rw [hβ x]
  rw [h1]
  exact hψ x

end Compatible






/-- Restriction along an identity is the identity. -/
theorem restrictPullbackHom_along_id {Z W : AlgebraicSpaces B S hS} {p : Z ⟶ W} (h : 𝟙 Z ≫ p = p)
    {M N : Modules.{u, u} B S hS W.1 W.2}
    (α : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    restrictPullbackHom (𝟙 Z) h α = α :=
  Functor.conjHom_id _ _
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_id h) α

end AlgebraicGeometry.Space

end
