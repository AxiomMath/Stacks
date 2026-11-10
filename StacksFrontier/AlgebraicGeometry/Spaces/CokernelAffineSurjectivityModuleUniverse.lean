module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian

/-!
# The cokernel clause of Stacks 03M1 for modules cartesian on affine charts, at any module universe

`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCartesian` and
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian` prove, for an
`𝒪_F`-module on the small étale site of an algebraic space `F` whose sections live in the universe
`u` of the schemes, that an epimorphism whose source and kernel are cartesian on affine charts is
surjective on the sections over an affine chart, and that being cartesian on affine charts is
stable under cokernels.  This file states the same chain for `Modules.{u, m}`, with sections in an
arbitrary universe `m`.  Nothing in the arguments wants the two universes to agree: the descent
along a faithfully flat algebra, the local surjectivity of an epimorphism of sheaves of modules and
the exactness of evaluation at a chart are all insensitive to the universe of the sections.

The module universe other than `u` that matters is `u + 1`: by
`AlgebraicGeometry.Space.smallEtaleInternalHom` the internal Hom of two `𝒪_F`-modules with
sections in `u` has its sections in `u + 1`, and its ideal-power quotients are cokernels in
`Modules.{u, u + 1}`.

## Main results

* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian'`: an epimorphism of modules
  whose source and kernel are cartesian on affine charts is surjective on the sections over an
  affine étale chart.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel_of_cartesian'`: being cartesian on
  affine charts is stable under cokernels.
* `AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian'`: the projection onto such
  a cokernel is surjective on the sections over an affine étale chart.
* `AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff'`: a section dies in the quotient by a sheaf
  submodule exactly when it is a section of that submodule.

## Implementation notes

Each statement carries the sheafification of abelian groups at the module universe and the
comparison of its weak equivalences with the locally bijective morphisms as instance arguments.
They are what the abelian structure of `Modules.{u, m}` is built from; at `m = u` instance search
supplies them, and the statements here then specialise to their namesakes without the prime.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

namespace AlgebraicGeometry.Space

section Implicit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The sheaf condition for a presheaf quotient of modules cartesian on affine charts, for a
finite family of affine charts covering an affine chart flatly in schemes, at every module
universe: `AlgebraicGeometry.Space.isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian` for
`Modules.{u, m}`. -/
theorem isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian'
    {K P : Modules.{u, m} B S hS F hF}
    {C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj}
    (a : K ⟶ P) (π : P.val ⟶ C) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    (hK : IsCartesianOnAffineCharts K) (hP : IsCartesianOnAffineCharts P)
    {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {ι : Type*} [Finite ι] (Y : ι → SmallEtale B S hS F) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i))
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fppfPrecoverage
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Presieve.IsSheafFor (C.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (Presieve.ofArrows Y g) := by
  classical
  obtain ⟨Pb, pr₁, pr₂, hpb⟩ : ∃ (Pb : ι → ι → SmallEtale B S hS F)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j),
      ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j) :=
    ⟨fun i j ↦ pullback (g i) (g j), fun i j ↦ pullback.fst (g i) (g j),
      fun i j ↦ pullback.snd (g i) (g j), fun i j ↦ IsPullback.of_hasPullback (g i) (g j)⟩
  have hpq : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j := fun i j ↦ (hpb i j).w
  have hPbaff : ∀ i j, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Pb i j)) := fun i j ↦
    SmallEtale.isAffine_of_isPullback_charts (hpb i j) hW (hY i) (hY j)
  let algY : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Y i)) := fun i ↦
    chartAlgebra (hF := hF) (g i)
  let algPb : ∀ i j, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Pb i j)) :=
    fun i j ↦ chartAlgebra (hF := hF) (pr₁ i j ≫ g i)
  let : Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (Y i)) :=
    SmallEtale.faithfullyFlat_pi_chartRing (hF := hF) Y g hW hY hfppf
  have hu : ∀ (i j : ι) (c : chartRing B S hS F hF W),
      chartRestrict (hF := hF) (pr₁ i j) (chartRestrict (hF := hF) (g i) c) =
        chartRestrict (hF := hF) (pr₁ i j ≫ g i) c := fun i j c ↦
    (RingHom.congr_fun (chartRestrict_comp (hF := hF) (g i) (pr₁ i j)) c).symm
  have hv : ∀ (i j : ι) (c : chartRing B S hS F hF W),
      chartRestrict (hF := hF) (pr₂ i j) (chartRestrict (hF := hF) (g j) c) =
        chartRestrict (hF := hF) (pr₁ i j ≫ g i) c := fun i j c ↦ by
    rw [show chartRestrict (hF := hF) (pr₁ i j ≫ g i) =
      chartRestrict (hF := hF) (pr₂ i j ≫ g j) from
        congrArg (chartRestrict (hF := hF)) (hpq i j)]
    exact (RingHom.congr_fun (chartRestrict_comp (hF := hF) (g j) (pr₂ i j)) c).symm
  let l : ∀ i j, chartRing B S hS F hF (Y i) →ₐ[chartRing B S hS F hF W]
      chartRing B S hS F hF (Pb i j) := fun i j ↦
    AlgHom.mk (chartRestrict (hF := hF) (pr₁ i j)) (hu i j)
  let r : ∀ i j, chartRing B S hS F hF (Y j) →ₐ[chartRing B S hS F hF W]
      chartRing B S hS F hF (Pb i j) := fun i j ↦
    AlgHom.mk (chartRestrict (hF := hF) (pr₂ i j)) (hv i j)
  obtain ⟨eP, heP⟩ : ∃ eP : ∀ i j, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Y i)) (chartRing B S hS F hF (Y j))
        ≃ₗ[chartRing B S hS F hF W] chartRing B S hS F hF (Pb i j),
      ∀ i j x y, eP i j (TensorProduct.tmul _ x y) = l i j x * r i j y := by
    choose e he using fun (i j : ι) ↦ SmallEtale.exists_tensorEquiv_chartRing_of_isPullback
      (hF := hF) (hpb i j) hW (hY i) (hY j)
    exact ⟨e, fun i j x y ↦ he i j x y⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ∀ i, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Y i)) (C.obj (op W)) ≃ₗ[chartRing B S hS F hF (Y i)]
        (C.obj (op (Y i)) : Type m),
      ∀ i n, e₁ i (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Y i)) n) =
        C.restrictₛₗ (g i).op n := by
    choose e he using fun i ↦ exists_baseChangeEquiv_sections_of_isPresheafCokernel a π hπ (g i)
      (hK W (Y i) hW (hY i) (g i)) (hP W (Y i) hW (hY i) (g i))
    exact ⟨e, he⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ∀ i j, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Pb i j)) (C.obj (op W)) ≃ₗ[chartRing B S hS F hF (Pb i j)]
        (C.obj (op (Pb i j)) : Type m),
      ∀ i j n, e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₁ i j ≫ g i).op n := by
    choose e he using fun (i j : ι) ↦
      exists_baseChangeEquiv_sections_of_isPresheafCokernel a π hπ (pr₁ i j ≫ g i)
        (hK W (Pb i j) hW (hPbaff i j) (pr₁ i j ≫ g i))
        (hP W (Pb i j) hW (hPbaff i j) (pr₁ i j ≫ g i))
    exact ⟨e, fun i j n ↦ he i j n⟩
  have he₂₁ : ∀ (i j : ι) (n : C.obj (op W)),
      e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₁ i j).op (C.restrictₛₗ (g i).op n) := fun i j n ↦
    (he₂ i j n).trans (C.map_comp_apply (g i).op (pr₁ i j).op n)
  have he₂₂ : ∀ (i j : ι) (n : C.obj (op W)),
      e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₂ i j).op (C.restrictₛₗ (g j).op n) := fun i j n ↦
    (he₂ i j n).trans (by
      rw [show (pr₁ i j ≫ g i).op = (g j).op ≫ (pr₂ i j).op from
        congrArg Quiver.Hom.op (hpq i j)]
      exact C.map_comp_apply (g j).op (pr₂ i j).op n)
  have he₁' : ∀ (i : ι) (c : chartRing B S hS F hF (Y i)) (n : C.obj (op W)),
      e₁ i (TensorProduct.tmul _ c n) =
        c • e₁ i (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Y i)) n) := fun i c n ↦ by
    rw [← LinearEquiv.map_smul]
    exact congrArg (e₁ i) (by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  have he₂' : ∀ (i j : ι) (c : chartRing B S hS F hF (Pb i j)) (n : C.obj (op W)),
      e₂ i j (TensorProduct.tmul _ c n) =
        c • e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) :=
          fun i j c n ↦ by
    rw [← LinearEquiv.map_smul]
    exact congrArg (e₂ i j) (by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  have key : ∀ (i j k : ι) (p : Pb i j ⟶ Y k)
      (ρ : chartRing B S hS F hF (Y k) →ₐ[chartRing B S hS F hF W] chartRing B S hS F hF (Pb i j))
      (_ : ∀ c, ρ c = chartRestrict (hF := hF) p c) (_ : ∀ n : C.obj (op W),
        e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
          C.restrictₛₗ p.op (C.restrictₛₗ (g k).op n))
      (x : TensorProduct (chartRing B S hS F hF W) (chartRing B S hS F hF (Y k))
        (C.obj (op W))),
      C.restrictₛₗ p.op (e₁ k x) = e₂ i j (TensorProduct.map ρ.toLinearMap LinearMap.id x) := by
    intro i j k p ρ hρ hE x
    induction x using TensorProduct.inductionOn with
    | tmul c n =>
      refine (congrArg (C.restrictₛₗ p.op) (he₁' k c n)).trans
        ((map_smulₛₗ (C.restrictₛₗ p.op) c _).trans ?_)
      rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        he₂', hE, he₁, hρ]
      rfl
    | add x y hx hy =>
      rw [map_add (e₁ k)]
      refine (map_add (C.restrictₛₗ p.op) _ _).trans ?_
      rw [hx, hy, map_add (TensorProduct.map ρ.toLinearMap LinearMap.id), map_add (e₂ i j)]
      rfl
  refine Stacks.Sites.isSheafFor_of_finite_tensor_descent _ Y g Pb pr₁ pr₂ hpq
    (chartRing B S hS F hF W) (fun i ↦ chartRing B S hS F hF (Y i))
    (fun i j ↦ chartRing B S hS F hF (Pb i j)) (C.obj (op W)) eP l r heP (Equiv.refl _)
    (fun i ↦ (e₁ i).toEquiv) (fun i j ↦ (e₂ i j).toEquiv) (fun i n ↦ (he₁ i n).symm)
    (fun i j x ↦ ?_) (fun i j x ↦ ?_)
  · exact key i j i (pr₁ i j) (l i j) (fun _ ↦ rfl) (he₂₁ i j) x
  · exact key i j j (pr₂ i j) (r i j) (fun _ ↦ rfl) (he₂₂ i j) x

/-- A presheaf quotient of modules cartesian on affine charts is separated for every covering
sieve of an affine étale chart, at every module universe:
`AlgebraicGeometry.Space.isSeparatedFor_of_isPresheafCokernel_of_cartesian` for
`Modules.{u, m}`. -/
theorem isSeparatedFor_of_isPresheafCokernel_of_cartesian'
    {K P : Modules.{u, m} B S hS F hF}
    {C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj}
    (a : K ⟶ P) (π : P.val ⟶ C) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    (hK : IsCartesianOnAffineCharts K) (hP : IsCartesianOnAffineCharts P)
    (Z : SmallEtale B S hS F)
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (T : Sieve Z) (hT : T ∈ SmallEtale.topology B S hS F Z) :
    Presieve.IsSeparatedFor (C.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (T : Presieve Z) := by
  obtain ⟨k, V, φ, hVaff, hmem, hcov, het⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hZ hT
  exact Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le _ T φ hmem
    (isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian' a π hπ hK hP hZ V φ hVaff
      (Scheme.etalePrecoverage_le_fppfPrecoverage _ het)).isSeparatedFor

/-- The arrows along which a section of the target of an epimorphism of modules lifts form a
covering sieve, at every module universe: `AlgebraicGeometry.Space.mem_topology_imageSieve_of_epi`
for `Modules.{u, m}`. -/
theorem mem_topology_imageSieve_of_epi'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {P Q : Modules.{u, m} B S hS F hF} (q : P ⟶ Q) [Epi q] (W : SmallEtale B S hS F)
    (n : Q.val.obj (op W)) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj).map
          q.val) n ∈
      SmallEtale.topology B S hS F W := by
  have hls := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    (J := (smallEtaleRingedSite B S hS F hF).J) q
  exact Presheaf.imageSieve_mem (smallEtaleRingedSite B S hS F hF).J
    ((PresheafOfModules.toPresheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj).map
        q.val) (U := op W) n

/-- A section of the target of an epimorphism of modules lifts over the members of a finite
covering family of affine charts of an affine chart which is flat in schemes, at every module
universe: `AlgebraicGeometry.Space.exists_finite_affine_ofArrows_lift_of_epi` for
`Modules.{u, m}`. -/
theorem exists_finite_affine_ofArrows_lift_of_epi'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {P Q : Modules.{u, m} B S hS F hF} (q : P ⟶ Q) [Epi q] (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (n : Q.val.obj (op W)) :
    ∃ (k : ℕ) (Z : Fin k → SmallEtale B S hS F) (φ : ∀ i, Z i ⟶ W),
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Z i))) ∧
        Sieve.ofArrows Z φ ∈ SmallEtale.topology B S hS F W ∧
        Presieve.ofArrows
            (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Z i))
            (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (φ i)) ∈
          Scheme.fppfPrecoverage
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        ∀ i, ∃ s : P.val.obj (op (Z i)),
          q.val.app (op (Z i)) s = Q.val.map (φ i).op n := by
  obtain ⟨k, Z, φ, hZaff, hφS, hφcov, hφet⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hW
      (mem_topology_imageSieve_of_epi' q W n)
  exact ⟨k, Z, φ, hZaff, hφcov,
    Scheme.etalePrecoverage_le_fppfPrecoverage _ hφet, fun i ↦ hφS i⟩

/-- A section which is a value of an epimorphism of modules over a chart is a value of the
morphism out of the presheaf quotient there, at every module universe:
`AlgebraicGeometry.Space.exists_cokernelDesc_app_eq_of_exists_val_app_eq` for `Modules.{u, m}`. -/
theorem exists_cokernelDesc_app_eq_of_exists_val_app_eq'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {P Q : Modules.{u, m} B S hS F hF} (q : P ⟶ Q)
    (hab' : (kernel.ι q).val ≫ q.val = 0) (X : SmallEtale B S hS F) (y : Q.val.obj (op X))
    (h : ∃ s : P.val.obj (op X), q.val.app (op X) s = y) :
    ∃ t : (cokernel (kernel.ι q).val).obj (op X),
      (cokernel.desc (kernel.ι q).val q.val hab').app (op X) t = y := by
  obtain ⟨s, hs⟩ := h
  exact ⟨(cokernel.π (kernel.ι q).val).app (op X) s,
    (SheafOfModules.cokernelDesc_app_π_app (kernel.ι q) q hab' (op X) s).trans hs⟩

/-- **An epimorphism of modules whose source and whose kernel are cartesian on affine charts is
surjective on the sections over every affine étale chart**, at every module universe:
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian` for `Modules.{u, m}`. -/
theorem surjective_val_app_of_epi_of_cartesian'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {P Q : Modules.{u, m} B S hS F hF} (q : P ⟶ Q) [Epi q]
    (hP : IsCartesianOnAffineCharts P)
    (hker : IsCartesianOnAffineCharts (kernel q))
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  have hab' : (kernel.ι q).val ≫ q.val = 0 := by
    rw [← SheafOfModules.comp_val, kernel.condition q]
    rfl
  have hπ := PresheafOfModules.isPresheafCokernel_cokernelπ (kernel.ι q).val
  have hpb : HasPullbacks (smallEtaleRingedSite B S hS F hF).C :=
    SmallEtale.instHasPullbacks B S hS F
  refine SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows (kernel.ι q) q hab'
    (fun Z s t hst => SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq
      (kernel.ι q) q _ (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι q) (kernel.condition q)) (kernelIsKernel q)) hab' Z s t hst)
    fun n => ?_
  obtain ⟨k, Z, φ, hZaff, hφcov, hφppf, hlift⟩ :=
    exists_finite_affine_ofArrows_lift_of_epi' q W hW n
  exact ⟨Fin k, Z, φ, ⟨fun _ _ ↦ have := hpb; inferInstance⟩,
    isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian' (kernel.ι q)
      (cokernel.π (kernel.ι q).val) hπ hker hP hW Z φ hZaff hφppf,
    hφcov, (fun i j T hT => isSeparatedFor_of_isPresheafCokernel_of_cartesian' (kernel.ι q)
      (cokernel.π (kernel.ι q).val) hπ hker hP _
      (SmallEtale.isAffine_pullback_charts (φ i) (φ j) hW (hZaff i) (hZaff j)) T hT),
    fun i ↦ exists_cokernelDesc_app_eq_of_exists_val_app_eq' q hab' (Z i) _ (hlift i)⟩

/-- The kernel of the canonical epimorphism of `f` onto its image is cartesian on affine charts
when the source and the target of `f` are, at every module universe:
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel_factorThruImage` for
`Modules.{u, m}`. -/
theorem isCartesianOnAffineCharts_kernel_factorThruImage'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (kernel (Abelian.factorThruImage f)) :=
  IsCartesianOnAffineCharts.of_iso
    (kernelIsoOfEq (Abelian.image.fac f).symm ≪≫
      kernelCompMono (Abelian.factorThruImage f) (Abelian.image.ι f))
    (isCartesianOnAffineCharts_kernel f hM hN)

/-- The canonical epimorphism of a morphism of modules cartesian on affine charts onto its image
is surjective on the sections over an affine étale chart, at every module universe:
`AlgebraicGeometry.Space.surjective_val_app_factorThruImage_of_cartesian` for
`Modules.{u, m}`. -/
theorem surjective_val_app_factorThruImage_of_cartesian'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((Abelian.factorThruImage f).val.app (op U)) :=
  surjective_val_app_of_epi_of_cartesian' (Abelian.factorThruImage f) hM
    (isCartesianOnAffineCharts_kernel_factorThruImage' f hM hN) U hU

/-- The image of a morphism of modules cartesian on affine charts is cartesian on affine charts,
at every module universe: `AlgebraicGeometry.Space.isCartesianOnAffineCharts_image_of_cartesian`
for `Modules.{u, m}`. -/
theorem isCartesianOnAffineCharts_image_of_cartesian'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (Abelian.image f) := by
  have hk : IsCartesianOnAffineCharts (kernel f) := isCartesianOnAffineCharts_kernel f hM hN
  have hki : IsCartesianOnAffineCharts (kernel (cokernel.π (kernel.ι f))) :=
    IsCartesianOnAffineCharts.of_iso (asIso (Abelian.factorThruImage (kernel.ι f))) hk
  have hiso : ∀ W : SmallEtale B S hS F, Function.Surjective
      ((Abelian.factorThruImage (kernel.ι f)).val.app (op W)) := fun W =>
    (bijective_moduleHom_app (Abelian.factorThruImage (kernel.ι f))
      (inv (Abelian.factorThruImage (kernel.ι f))) (IsIso.hom_inv_id _)
      (IsIso.inv_hom_id _) W).2
  exact IsCartesianOnAffineCharts.of_iso (Abelian.coimageIsoImage f)
    (isCartesianOnAffineCharts_cokernel (kernel.ι f) (cokernel.π (kernel.ι f))
      (fun W hW => surjective_val_app_of_epi_of_cartesian' (cokernel.π (kernel.ι f)) hM hki W hW)
      (fun W _ => SheafOfModules.exact_val_app_cokernel_π (kernel.ι f) (op W) (hiso W))
      hk hM)

/-- **The projection onto the cokernel of a morphism of modules cartesian on affine charts is
surjective on the sections over an affine étale chart**, at every module universe:
`AlgebraicGeometry.Space.surjective_val_app_cokernel_π_of_cartesian` for `Modules.{u, m}`. -/
theorem surjective_val_app_cokernel_π_of_cartesian'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((cokernel.π f).val.app (op U)) :=
  surjective_val_app_of_epi_of_cartesian' (cokernel.π f) hN
    (isCartesianOnAffineCharts_image_of_cartesian' f hM hN) U hU

/-- **Being cartesian on affine charts is stable under cokernels**, at every module universe:
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel_of_cartesian` for
`Modules.{u, m}`. -/
theorem isCartesianOnAffineCharts_cokernel_of_cartesian'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M N : Modules.{u, m} B S hS F hF} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (cokernel f) :=
  isCartesianOnAffineCharts_cokernel f (cokernel.π f)
    (fun U hU => surjective_val_app_cokernel_π_of_cartesian' f hM hN U hU)
    (fun U hU => SheafOfModules.exact_val_app_cokernel_π f (op U)
      (surjective_val_app_factorThruImage_of_cartesian' f hM hN U hU))
    hM hN

end Implicit

section Explicit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A section dies in the quotient by a sheaf submodule exactly when it is a section of that
submodule**, at every module universe: `AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff` for
`Modules.{u, m}`. -/
theorem cokernel_π_app_eq_zero_iff'
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M : Modules.{u, m} B S hS F hF} (P : M.Submodule)
    (X : (SmallEtale B S hS F)ᵒᵖ) (s : M.val.obj X) :
    (cokernel.π P.ι).val.app X s = 0 ↔ s ∈ P.obj X := by
  let T := SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) X
  let _ : T.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) X
  have hex := (ShortComplex.exact_cokernel P.ι).map_of_mono_of_preservesKernel T
    inferInstance inferInstance
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex s hs
    exact ht ▸ t.property
  · exact congrArg (fun k : P.toSheafOfModules ⟶ cokernel P.ι => k.val.app X ⟨s, hs⟩)
      (cokernel.condition P.ι)

end Explicit

end AlgebraicGeometry.Space

end
