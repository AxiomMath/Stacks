module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ChartSectionsDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FinitePresentationAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules

/-!
# A quasi-coherent module finitely generated over a Noetherian chart is coherent

Let `a : (Sch/U) ⟶ 𝒳` be a smooth surjective 1-morphism to a locally Noetherian algebraic stack,
with `U` affine, and `u = a(id_U)`.  A quasi-coherent `𝒪_𝒳`-module `ℱ` whose sections over `u`
form a finitely generated `Γ(U)`-module is coherent (Stacks 0GR6): the sections over `u` are of
finite presentation, `Γ(U)` being Noetherian; over every object over an affine scheme which maps
to `u` the sections are their base change; and finite presentation descends along the finite
faithfully flat coverings by such objects.  Finite presentation of the sections over all objects
over affine schemes then gives finite global presentations on the fppf slices.

## Main results

* `AlgebraicGeometry.FibredSite.isFinitePresentationOnSite_of_finitePresentation_obj`: a
  quasi-coherent module with finitely presented sections over affine objects is of finite
  presentation on the fppf site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.finitePresentation_obj_of_chart`
* `AlgebraicGeometry.Stack.AlgebraicStacks.isCoherent_of_fg_chart`

## References

* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS}
  {hp : p.IsFiberedInGroupoids}

attribute [local instance] objModule

variable (B S hS p hp) in
/-- **A quasi-coherent module with finitely presented sections over an affine object has a
finite global presentation on the fppf slice at that object.** -/
theorem hasFiniteGlobalPresentation_over_of_finitePresentation
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite) {y : 𝒳} (hy : IsAffineOver B S hS (p.obj y))
    (hfp : Module.FinitePresentation (objRing B S hS p y) (F.val.obj (op y))) :
    (F.over y).HasFiniteGlobalPresentation := by
  let J := BigFppfOver.associatedTopology B S hS p .fppf
  have : ∀ X : 𝒳, HasSheafify (J.over X) AddCommGrpCat.{u} := fun X =>
    have := essentiallySmall_over B S hS p hp X
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have : ∀ X : 𝒳, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u} := fun X =>
    wEqualsLocallyBijective_over B S hS p hp .fppf X
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' (objRing B S hS p y)
    (F.val.obj (op y))
  let s : Fin n → F.val.obj (op y) := fun i => f (Pi.single i 1)
  let t : Fin m → Fin n → (ringStructureSheafCore B S hS p hp .fppf).obj.obj (op y) :=
    fun j i => g (Pi.single j 1) i
  have hrel : ∀ j, ∑ i, t j i • s i = 0 := by
    intro j
    have : ∑ i, t j i • s i = f (g (Pi.single j 1)) := by
      conv_rhs => rw [show g (Pi.single j 1) = ∑ i, g (Pi.single j 1) i • Pi.single i 1 by
        ext k
        simp [Pi.single_apply]]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul f _ _).symm
    rw [this]
    exact (hfg _).2 ⟨_, rfl⟩
  have hA : ∀ V : 𝒳, Sieve.generate (fun W (_ : W ⟶ V) => IsAffineOver B S hS (p.obj W)) ∈
      J V := fun V =>
    BigFppfOver.associatedTopology_le_fppf B S hS p .etale V
      (mem_etale_of_forall_isAffine B S hS p hp V _ fun W f hW => ⟨W, 𝟙 W, f, hW,
        Category.id_comp f⟩)
  have hgen : Stacks.SheafOfModules.GeneratesLocally J F.val s := by
    intro V f' x
    refine ⟨_, hA V, ?_⟩
    rintro W _ ⟨W', h, g', hg', rfl⟩
    obtain ⟨b, hb⟩ := exists_sum_restriction_eq F hF (g' ≫ f') hy hg' f hf
      (F.val.restrictₛₗ g'.op x)
    refine ⟨fun i => (ringStructureSheafCore B S hS p hp .fppf).obj.map h.op (b i), ?_⟩
    have e := congrArg (F.val.restrictₛₗ h.op) hb
    rw [map_sum] at e
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (e.trans ?_)
    · rw [map_smulₛₗ]
      congr 1
      change _ = F.val.map h.op (F.val.map (g' ≫ f').op (s i))
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, ← Category.assoc]
      rfl
    · exact (PresheafOfModules.map_comp_apply F.val g'.op h.op x).symm
  have hall : ∀ (W : 𝒳) (g'' : W ⟶ y)
      (a : Fin n → ToType ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op W))),
      ∑ i, a i • Stacks.SheafOfModules.res F g'' (s i) = 0 →
      ∃ T : Sieve W, T ∈ J W ∧ ∀ (Z : 𝒳) (h : Z ⟶ W), T h →
        ∃ c : Fin m → ToType ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op Z)),
          ∀ i, Stacks.SheafOfModules.resR _ h (a i) =
            ∑ j, c j * Stacks.SheafOfModules.resR _ (h ≫ g'') (t j i) := by
    intro W g'' a ha
    refine ⟨_, hA W, ?_⟩
    rintro Z _ ⟨Z', k, h', hZ', rfl⟩
    let b : Fin n → objRing B S hS p Z' := fun i =>
      (ringStructureSheafCore B S hS p hp .fppf).obj.map h'.op (a i)
    have hb : ∑ i, b i • F.val.restrictₛₗ (h' ≫ g'').op (f (Pi.single i 1)) = 0 := by
      have e := congrArg (F.val.restrictₛₗ h'.op) ha
      rw [map_sum, map_zero] at e
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e
      rw [map_smulₛₗ]
      exact congrArg (b i • ·) (PresheafOfModules.map_comp_apply F.val g''.op h'.op (s i))
    obtain ⟨c, hc⟩ := exists_coeffs_restriction F hF (h' ≫ g'') hy hZ' f g hf hfg b hb
    refine ⟨fun j => (ringStructureSheafCore B S hS p hp .fppf).obj.map k.op (c j), fun i => ?_⟩
    let R := ringStructureSheafCore B S hS p hp .fppf
    have e₁ : Stacks.SheafOfModules.resR R (k ≫ h') (a i) =
        Stacks.SheafOfModules.resR R k (b i) :=
      (Stacks.SheafOfModules.resR_resR R h' k (a i)).symm
    have e₂ : ∀ j, Stacks.SheafOfModules.resR R ((k ≫ h') ≫ g'') (t j i) =
        Stacks.SheafOfModules.resR R k
          (((BigFppfOver.toScheme B S hS).map (p.map (h' ≫ g''))).appTop.hom
            (g (Pi.single j 1) i)) := fun j =>
      (congrArg (fun q => Stacks.SheafOfModules.resR R q (t j i)) (Category.assoc k h' g'')).trans
        (Stacks.SheafOfModules.resR_resR R (h' ≫ g'') k (t j i)).symm
    rw [e₁, hc i]
    exact (map_sum (R.obj.map k.op).hom _ _).trans
      (Finset.sum_congr rfl fun j _ => (map_mul (R.obj.map k.op).hom _ _).trans
        (congrArg (_ * ·) (e₂ j).symm))
  obtain ⟨P, hP⟩ := Stacks.SheafOfModules.exists_isFinite_presentation_over_of_relations F s t
    hrel hgen hall
  have := hasWeakSheafify_over B S hS p hp .fppf y
  exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation' P hP

variable (B S hS p hp) in
/-- **A quasi-coherent module whose sections over affine objects are finitely presented is of
finite presentation** on the fppf site (Stacks 03DL (7)). -/
theorem isFinitePresentationOnSite_of_finitePresentation_obj
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : F.IsQuasicoherentOnSite)
    (hfp : ∀ y, IsAffineOver B S hS (p.obj y) →
      Module.FinitePresentation (objRing B S hS p y) (F.val.obj (op y))) :
    F.IsFinitePresentationOnSite := by
  constructor
  intro U
  obtain ⟨I, y, φ, haff, hcov⟩ := exists_affine_etale_ofArrows B S hS p hp U
  exact ⟨I, y, φ, BigFppfOver.associatedTopology_le_fppf B S hS p .etale U hcov, fun j =>
    hasFiniteGlobalPresentation_over_of_finitePresentation B S hS p hp F hF (haff j)
      (hfp _ (haff j))⟩

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  {a : schemeStack.{u, w} B S hS U ⟶ 𝒳}

attribute [local instance] objModule

/-- **Finite presentation spreads out from a chart.**  If the sections over `u = a(id_U)` of a
quasi-coherent module are finitely presented, so are its sections over every object over an
affine scheme. -/
theorem finitePresentation_obj_of_chart (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (hu : IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)))
    {M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hM : M.IsQuasicoherentOnSite)
    (hfp : Module.FinitePresentation (objRing B S hS 𝒳.val.val.p (chartObject a))
      (M.val.obj (op (chartObject a)))) {y : 𝒳.val.val.obj}
    (hy : IsAffineOver B S hS (𝒳.val.val.p.obj y)) :
    Module.FinitePresentation (objRing B S hS 𝒳.val.val.p y) (M.val.obj (op y)) := by
  let p := 𝒳.val.val.p
  obtain ⟨n, z, φ, hzaff, hmem, -, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le B S hS p 𝒳.val.isFiberedInGroupoids hy
      (chartSieve_mem a hsm hsurj y)
  let : ∀ i, Algebra (objRing B S hS p y) (objRing B S hS p (z i)) := fun i =>
    objAlgebra B S hS p (φ i)
  let : ∀ i, Module (objRing B S hS p y) (M.val.obj (op (z i))) := fun i =>
    Module.compHom _ (algebraMap (objRing B S hS p y) (objRing B S hS p (z i)))
  have : ∀ i, IsScalarTower (objRing B S hS p y) (objRing B S hS p (z i))
      (M.val.obj (op (z i))) := fun i => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) := hy
  have : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (z i))) := hzaff
  have : Module.FaithfullyFlat (objRing B S hS p y) (∀ i, objRing B S hS p (z i)) :=
    _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
      (fun i => (BigFppfOver.toScheme B S hS).map (p.map (φ i))) hfppf fun _ => rfl
  have : ∀ i, Module.FinitePresentation (objRing B S hS p (z i)) (M.val.obj (op (z i))) := by
    intro i
    obtain ⟨d⟩ := hmem i
    let := objAlgebra B S hS p d
    let : Module (objRing B S hS p (chartObject a)) (M.val.obj (op (z i))) :=
      Module.compHom _ (algebraMap (objRing B S hS p (chartObject a)) (objRing B S hS p (z i)))
    have : IsScalarTower (objRing B S hS p (chartObject a)) (objRing B S hS p (z i))
        (M.val.obj (op (z i))) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hb := bijective_liftBaseChange_of_eq_restriction M hM d hu (hzaff i)
      (restrictionLinear M d) fun _ => rfl
    exact Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective _ hb)
  exact Module.FinitePresentation.of_forall_bijective_liftBaseChange_pi
    (fun i => objRing B S hS p (z i)) (objRing B S hS p y) (M.val.obj (op y))
    (fun i => M.val.obj (op (z i))) (fun i => restrictionLinear M (φ i))
    (fun i => bijective_liftBaseChange_of_eq_restriction M hM (φ i) hy (hzaff i) _ fun _ => rfl)

/-- **A quasi-coherent module finitely generated over a Noetherian affine chart is coherent**
(Stacks 0GR6). -/
theorem isCoherent_of_fg_chart (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳)
    (hu : IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)))
    [IsNoetherianRing (objRing B S hS 𝒳.val.val.p (chartObject a))]
    {M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hM : M.IsQuasicoherentOnSite)
    (hfg : Module.Finite (objRing B S hS 𝒳.val.val.p (chartObject a))
      (M.val.obj (op (chartObject a)))) :
    IsCoherent B S hS 𝒳 M :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 M).2 <|
    isFinitePresentationOnSite_of_finitePresentation_obj B S hS _ _ M hM fun _ hy =>
      finitePresentation_obj_of_chart hsm hsurj hu hM (Module.finitePresentation_of_finite _ _) hy

end AlgebraicGeometry.Stack.AlgebraicStacks

end
