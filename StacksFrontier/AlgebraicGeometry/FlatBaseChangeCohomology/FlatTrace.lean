module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FiniteLocallyFreeCanonical

/-!
# Traces of functionals on the base for a flat base change over a separated scheme

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine and `Γ(S, ⊤) ⟶ Γ(T, ⊤)` flat, and let
`F` be a quasi-coherent `𝒪_X`-module. When `X` is separated over `S`, the canonical comparison
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)` is bijective over every quasi-compact open `U`
of `X`: cover `U` by finitely many affine opens, whose pairwise intersections are affine; the
sheaf sequence of `F` on that cover is carried through the exact functor `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -`,
which commutes with the finite products, and the comparison is known over the affine opens
([Stacks, Tag 02KG]).

Over every open this lets a `Γ(S, ⊤)`-linear functional `f` on `Γ(T, ⊤)` act on `p_* p^* F`,
`b ⊗ x ↦ f(b) x`, as a morphism of `𝒪_X`-modules `p_* p^* F ⟶ F`, the *trace* of `f`. It undoes the
twisted unit `x ↦ b • p^* x` up to the scalar `f(b)`, and when `Γ(T, ⊤)` is a free
`Γ(S, ⊤)`-module the traces of all functionals detect sections of `p_* p^* F`. This is the
mechanism of the proof of [Stacks, Tag 0CKW] for a finite locally free `q`
(`Stacks.Tag0CKW.trace`), here for a flat `q` with infinitely generated `Γ(T, ⊤)`, such as an
infinite extension of fields, where the finite dual basis of that proof does not exist.

## Main results

* `Stacks.FlatTrace.bijective_sectionsBaseChangeMap_of_cover`: bijectivity of the comparison
  over an open with a finite affine cover with affine pairwise intersections.
* `Stacks.FlatTrace.bijective_sectionsBaseChangeMap_of_isSeparated`: bijectivity over every
  quasi-compact open of a scheme separated over `S`.
* `Stacks.FlatTrace.traceOf`: the trace of a functional, given that bijectivity.
* `Stacks.FlatTrace.twistedUnit_comp_traceOf`: the twisted unit followed by the trace of `f` is
  multiplication by `f(b)`.
* `Stacks.FlatTrace.eq_zero_of_forall_traceOf_app_eq_zero`: the traces detect sections.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace Stacks.FlatTrace

/-! ### Linear algebra -/

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (M : ι → Type u)
  [∀ a, AddCommGroup (M a)] [∀ a, Module A (M a)]

/-- **Base change of a map into a finite product, read componentwise.** -/
theorem piRight_lTensor_pi_apply {N : Type u} [AddCommGroup N] [Module A N]
    (f : ∀ a, N →ₗ[A] M a) (a : ι) (w : B ⊗[A] N) :
    TensorProduct.piRight A B B M (LinearMap.lTensor B (LinearMap.pi f) w) a =
      LinearMap.lTensor B (f a) w := by
  induction w with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **Base change of a map out of a finite product, read through the comparison.** -/
theorem lTensor_comp_proj_apply {P : Type u} [AddCommGroup P] [Module A P] (a : ι)
    (g : M a →ₗ[A] P) (z : B ⊗[A] (∀ b, M b)) :
    LinearMap.lTensor B (g ∘ₗ (LinearMap.proj a : (∀ b, M b) →ₗ[A] M a)) z =
      LinearMap.lTensor B g (TensorProduct.piRight A B B M z a) := by
  induction z with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Algebra

/-- **A base change of a map into a finite product vanishes if its components do.** -/
private theorem lTensor_pi_eq_zero {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] {ι : Type u} [Finite ι] (M : ι → Type u)
    [∀ a, AddCommGroup (M a)] [∀ a, Module A (M a)] (f : ∀ a, N →ₗ[A] M a) (w : B ⊗[A] N)
    (h : ∀ a, LinearMap.lTensor B (f a) w = 0) : LinearMap.lTensor B (LinearMap.pi f) w = 0 := by
  classical
  have := Fintype.ofFinite ι
  refine (TensorProduct.piRight A B B M).injective ?_
  rw [map_zero]
  funext a
  rw [piRight_lTensor_pi_apply]
  exact h a

/-- **The functionals on a free module detect the elements of its tensor products.** If `B` is a
free `A`-module and `z ∈ B ⊗_A M` is killed by `f ⊗ M` for every `A`-linear `f : B ⟶ A`, then
`z = 0`: in a basis of `B`, `f ⊗ M` for the coordinate functionals are the coordinates of `z`. -/
theorem eq_zero_of_forall_lid_rTensor_eq_zero {A B M : Type u} [CommRing A] [AddCommGroup B]
    [Module A B] [Module.Free A B] [AddCommGroup M] [Module A M] (z : B ⊗[A] M)
    (h : ∀ f : B →ₗ[A] A, TensorProduct.lid A M (LinearMap.rTensor M f z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis A B
  let e : B ⊗[A] M ≃ₗ[A] (Module.Free.ChooseBasisIndex A B →₀ M) :=
    (LinearEquiv.rTensor M b.repr).trans (TensorProduct.finsuppScalarLeft A M _)
  apply e.injective
  rw [map_zero]
  ext i
  have key (w : B ⊗[A] M) :
      e w i = TensorProduct.lid A M (LinearMap.rTensor M (b.coord i) w) := by
    induction w with
    | tmul x m =>
      simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply, Module.Basis.coord_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  rw [key, h]
  rfl

/-! ### Bijectivity over a quasi-compact open -/

section Cover

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-- **Restriction to an open cover is injective on sections.** -/
private theorem injective_pi_baseResHom_of_cover (iX : X ⟶ S) (F : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (U : X.Opens) (hVle : ∀ a, V a ≤ U) (hcover : U ≤ ⨆ a, V a) :
    letI : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
    Function.Injective (LinearMap.pi fun a => baseResHom iX F (hVle a)) := by
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  intro s t hst
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
    V U (fun a => homOfLE (hVle a)) hcover s t fun a => congrFun hst a

/-- **The sheaf sequence of `F` on an open cover is exact**: a family of sections over the members
of the cover glues to a section over `U` exactly when it agrees on the pairwise intersections. -/
private theorem exact_pi_baseResHom_of_cover (iX : X ⟶ S) (F : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (U : X.Opens) (hVle : ∀ a, V a ≤ U) (hcover : U ≤ ⨆ a, V a) :
    letI : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
    Function.Exact (LinearMap.pi fun a => baseResHom iX F (hVle a))
      (LinearMap.pi fun ab : ι × ι =>
        baseResHom iX F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) ∘ₗ
            LinearMap.proj (φ := fun a => ↑Γ(F, V a)) ab.1 -
          baseResHom iX F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) ∘ₗ
            LinearMap.proj (φ := fun a => ↑Γ(F, V a)) ab.2) := by
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  intro y
  constructor
  · intro hy
    have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V y := fun i j => by
      have hc := congrFun hy (i, j)
      simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero] at hc
      exact hc
    obtain ⟨s, hs, -⟩ :=
      TopCat.Sheaf.existsUnique_gluing' ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
        V U (fun a => homOfLE (hVle a)) hcover y hcompat
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext ab
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero]
    rw [Stacks.Tag0CKW.baseResHom_trans, Stacks.Tag0CKW.baseResHom_trans]

/-- **The degree-zero comparison is bijective over an open with a finite affine cover whose
pairwise intersections are affine**, for a flat `Γ(S, ⊤) ⟶ Γ(T, ⊤)`. The sheaf sequence of `F`
on the cover is a three-term exact sequence of `Γ(S, ⊤)`-modules; `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -` is exact
and commutes with the finite products, and the comparison is bijective over the members of the
cover and over their intersections, which are affine. -/
theorem bijective_sectionsBaseChangeMap_of_cover (H : IsPullback p k iX q) [IsAffine S]
    [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (hV : ∀ a, IsAffineOpen (V a))
    (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b)) (U : X.Opens) (hVle : ∀ a, V a ≤ U)
    (hcover : U ≤ ⨆ a, V a) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  classical
  have := Fintype.ofFinite ι
  let := baseAlgebra q
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let : ∀ W : X.Opens, Module Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let : ∀ W : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hq
  refine ⟨injective_iff_map_eq_zero _ |>.2 fun z hz => ?_, fun t => ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap _
      (injective_pi_baseResHom_of_cover iX F V U hVle hcover) ?_
    rw [map_zero]
    refine lTensor_pi_eq_zero _ _ _ fun a => ?_
    refine (bijective_sectionsBaseChangeMap_of_isAffineOpen H F (hV a)).1 ?_
    rw [map_zero, sectionsBaseChangeMap_comm_res H F (hVle a) z, hz, map_zero]
  choose z hz using fun a : ι =>
    (bijective_sectionsBaseChangeMap_of_isAffineOpen H F (hV a)).2
      (pullbackBaseResHom k p F (hVle a) t)
  set e := TensorProduct.piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤) (fun a : ι => ↑Γ(F, V a)) with hedef
  have hZ : ∀ a, e (e.symm z) a = z a := fun a => congrFun (e.apply_symm_apply z) a
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact Γ(T, ⊤)
    (exact_pi_baseResHom_of_cover iX F V U hVle hcover) (e.symm z)).mp <| by
    refine lTensor_pi_eq_zero _ _ _ fun ab => ?_
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
      lTensor_comp_proj_apply (fun a : ι => (Γ(F, V a) : Type u)) ab.1,
      lTensor_comp_proj_apply (fun a : ι => (Γ(F, V a) : Type u)) ab.2, hZ, hZ]
    refine (bijective_sectionsBaseChangeMap_of_isAffineOpen H F (hVV ab.1 ab.2)).1 ?_
    rw [sectionsBaseChangeMap_comm_res H F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) (z ab.1),
      sectionsBaseChangeMap_comm_res H F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) (z ab.2),
      hz ab.1, hz ab.2, Stacks.Tag0CKW.pullbackBaseResHom_trans,
      Stacks.Tag0CKW.pullbackBaseResHom_trans]
  refine ⟨w, TopCat.Sheaf.eq_of_locally_eq'
    ⟨((Scheme.Modules.pullback p).obj F).presheaf,
      Scheme.Modules.isSheaf ((Scheme.Modules.pullback p).obj F)⟩
    (fun a : ι => p ⁻¹ᵁ V a) (p ⁻¹ᵁ U)
    (fun a => homOfLE (Scheme.Hom.preimage_mono p (hVle a)))
    (by rw [← Scheme.Hom.preimage_iSup]; exact Scheme.Hom.preimage_mono p hcover)
    (sectionsBaseChangeMap H F U w) t fun a => ?_⟩
  change pullbackBaseResHom k p F (hVle a) (sectionsBaseChangeMap H F U w) = _
  rw [← sectionsBaseChangeMap_comm_res H F (hVle a) w, ← piRight_lTensor_pi_apply
    (fun a : ι => ↑Γ(F, V a)) (fun a => baseResHom iX F (hVle a)) a w, ← hedef, hw, hZ, hz a]
  rfl

/-- **The degree-zero comparison is bijective over every quasi-compact open of a scheme
separated over the affine base**, for a flat `Γ(S, ⊤) ⟶ Γ(T, ⊤)`: such an open has a finite
cover by affine opens, and their pairwise intersections are affine because `X` is separated. -/
theorem bijective_sectionsBaseChangeMap_of_isSeparated (H : IsPullback p k iX q) [IsAffine S]
    [IsAffine T] [IsSeparated iX] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom) (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = iX ≫ terminal.from S from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨s, hsU⟩ := hU.elim_finite_subcover
    (fun a : Stacks.Tag0CKW.affineOpensIn U => ((a.1 : X.Opens) : Set X))
    (fun a => (a.1 : X.Opens).isOpen)
    (fun x hx => Set.mem_iUnion.2 (Opens.mem_iSup.1 (Stacks.Tag0CKW.le_iSup_affineOpensIn U hx)))
  refine bijective_sectionsBaseChangeMap_of_cover H F hq (ι := s)
    (fun a => (a.1.1 : X.Opens)) (fun a => a.1.1.2)
    (fun a b => IsAffineOpen.inf a.1.1.2 b.1.1.2) U (fun a => a.1.2) ?_
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hsU hx)
  exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

end Cover

/-! ### The trace of a functional on the base -/

section Trace

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
  (F : X.Modules) [F.IsQuasicoherent]
  (hbij : ∀ U : X.Opens,
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U))

/-- The canonical comparison `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ≅ Γ(p^* F, p⁻¹U)`, over an arbitrary
open of `X`. -/
def sectionsBaseChangeEquivOf (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃ₗ[Γ(T, ⊤)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  LinearEquiv.ofBijective (sectionsBaseChangeMap H F U) (hbij U)

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- The comparison `sectionsBaseChangeEquivOf` sends `b ⊗ x` to `b • p^* x`. -/
theorem sectionsBaseChangeEquivOf_tmul (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    sectionsBaseChangeEquivOf H F hbij U (b ⊗ₜ[Γ(S, ⊤)] x) = b • pullbackUnitSections p F U x :=
  sectionsBaseChangeMap_tmul H F U b x

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- The inverse of `sectionsBaseChangeEquivOf` carries the action of `r ∈ Γ(X, U)` through `p` to
the action of `r` on the right tensor factor. -/
theorem sectionsBaseChangeEquivOf_symm_smul (U : X.Opens) (r : Γ(X, U))
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (sectionsBaseChangeEquivOf H F hbij U).symm ((p.app U).hom r • y) =
      LinearMap.lTensor Γ(T, ⊤) (Stacks.Tag0CKW.sectionsSmul F U r)
        ((sectionsBaseChangeEquivOf H F hbij U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquivOf H F hbij U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  induction z with
  | tmul b x =>
    rw [LinearMap.lTensor_tmul, sectionsBaseChangeEquivOf_tmul, sectionsBaseChangeEquivOf_tmul]
    change (p.app U).hom r • (b • _) = b • pullbackUnitSections p F U (r • x)
    rw [pullbackUnitSections_smul p F U r x]
    change (p.app U).hom r • ((k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        pullbackUnitSections p F U x) =
      (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        ((p.app U).hom r • pullbackUnitSections p F U x)
    rw [← mul_smul, ← mul_smul, mul_comm]
  | add z w hz hw => rw [map_add, smul_add, hz, hw, map_add, map_add]

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- The inverse of `sectionsBaseChangeEquivOf` commutes with restriction from `p⁻¹U` to `p⁻¹V`,
which corresponds to restriction from `U` to `V` on the right tensor factor. -/
theorem sectionsBaseChangeEquivOf_symm_res {U V : X.Opens} (h : V ≤ U)
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule iX F V
    (sectionsBaseChangeEquivOf H F hbij V).symm
        (((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p h)).op y) =
      LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F h)
        ((sectionsBaseChangeEquivOf H F hbij U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule iX F V
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquivOf H F hbij U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  exact (sectionsBaseChangeMap_comm_res H F h z).symm

/-- The trace of a `Γ(S, ⊤)`-linear functional `f` on `Γ(T, ⊤)`, on the sections of
`p_* p^* F` over one open: `b ⊗ x ↦ f(b) x` read through the comparison. -/
def traceSectionsOf (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) (U : X.Opens) :
    Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U) →ₗ[Γ(X, U)]
      Γ(F, U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  { toFun := fun y => TensorProduct.lid Γ(S, ⊤) Γ(F, U)
      (LinearMap.rTensor Γ(F, U) f
        ((sectionsBaseChangeEquivOf H F hbij U).symm (Stacks.Tag0CKW.pushforwardSection y)))
    map_add' := fun y y' => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquivOf H F hbij U).symm (Stacks.Tag0CKW.pushforwardSection y +
            Stacks.Tag0CKW.pushforwardSection y'))) = _
      simp only [map_add]
    map_smul' := fun r y => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquivOf H F hbij U).symm
            ((p.app U).hom r • Stacks.Tag0CKW.pushforwardSection y))) = r • _
      rw [sectionsBaseChangeEquivOf_symm_smul H F hbij]
      induction (sectionsBaseChangeEquivOf H F hbij U).symm
          (Stacks.Tag0CKW.pushforwardSection y) with
      | tmul b x =>
        simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        change (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • (r • x) =
          r • ((iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x)
        rw [← mul_smul, ← mul_smul, mul_comm]
      | add z w hz hw => simp only [map_add, smul_add, hz, hw] }

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- The trace `traceSectionsOf` of `f` sends `b • p^* x` to `f(b) • x`. -/
theorem traceSectionsOf_apply_tmul (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    traceSectionsOf H F hbij f U (b • pullbackUnitSections p F U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
    ((sectionsBaseChangeEquivOf H F hbij U).symm (b • pullbackUnitSections p F U x))) = _
  rw [← sectionsBaseChangeEquivOf_tmul H F hbij U b x, LinearEquiv.symm_apply_apply,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- The trace of a functional on `Γ(T, ⊤)`, as a morphism of `𝒪_X`-modules `p_* p^* F ⟶ F`. -/
def traceOf (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ⟶ F :=
  Stacks.Tag0CKW.homOfSections (traceSectionsOf H F hbij f) fun {U V} i y => by
    let := baseAlgebra q
    let := baseModule iX F U
    let := baseModule iX F V
    change TensorProduct.lid Γ(S, ⊤) Γ(F, V) (LinearMap.rTensor Γ(F, V) f
      ((sectionsBaseChangeEquivOf H F hbij V).symm
        (((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p (leOfHom i))).op
          (Stacks.Tag0CKW.pushforwardSection y)))) =
      F.presheaf.map i.op (TensorProduct.lid Γ(S, ⊤) Γ(F, U)
        (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquivOf H F hbij U).symm (Stacks.Tag0CKW.pushforwardSection y))))
    rw [sectionsBaseChangeEquivOf_symm_res H F hbij]
    induction (sectionsBaseChangeEquivOf H F hbij U).symm
        (Stacks.Tag0CKW.pushforwardSection y) with
    | tmul b x =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact ((baseResHom iX F (leOfHom i)).map_smul (f b) x).symm
    | add z w hz hw => simp only [map_add, hz, hw]

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- On sections over `U`, the twisted unit `x ↦ b • p^* x` followed by the trace `traceOf` of `f`
sends `x` to `f(b) • x`. -/
theorem traceOf_app_twistedUnit_app (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (traceOf H F hbij f).app U ((Stacks.Tag0CKW.twistedUnit k p F b).app U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [Stacks.Tag0CKW.twistedUnit_app]
  exact traceSectionsOf_apply_tmul H F hbij f U b x

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- **The trace undoes the twisted unit up to the functional.** `x ↦ b • p^* x` followed by
the trace of `f` is multiplication by `f(b)`. -/
theorem twistedUnit_comp_traceOf (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) :
    Stacks.Tag0CKW.twistedUnit k p F b ≫ traceOf H F hbij f =
      (Scheme.smulEnd X ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b))).asHom.app F := by
  let := baseAlgebra q
  ext U x
  let := baseModule iX F U
  refine (traceOf_app_twistedUnit_app H F hbij f b U x).trans ?_
  change (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x =
    X.presheaf.map (isTerminalTop.from U).op ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b)) • x
  congr 1
  exact (congrArg (fun m : Γ(S, ⊤) ⟶ Γ(X, U) => m.hom (f b))
    (Scheme.Hom.appLE_map iX (le_preimage_top iX ⊤) (isTerminalTop.from U).op)).symm

end Trace

/-! ### The traces detect sections -/

section Detect

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
  (F : X.Modules) [F.IsQuasicoherent]
  (hbij : ∀ U : X.Opens,
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U))

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- **The traces of all functionals detect the sections of `p_* p^* F`**, when `Γ(T, ⊤)` is a
free `Γ(S, ⊤)`-module: through the comparison a section is an element of
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U)`, on which the trace of `f` is `f ⊗ Γ(F, U)`. -/
theorem eq_zero_of_forall_traceOf_app_eq_zero
    (hfree : letI := baseAlgebra q; Module.Free Γ(S, ⊤) Γ(T, ⊤)) (U : X.Opens)
    (y : Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U))
    (h : ∀ f : (letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)),
      (traceOf H F hbij f).app U y = 0) : y = 0 := by
  let := baseAlgebra q
  let := baseModule iX F U
  obtain ⟨z, hz⟩ := (sectionsBaseChangeEquivOf H F hbij U).surjective
    (Stacks.Tag0CKW.pushforwardSection y)
  have hz0 : z = 0 := eq_zero_of_forall_lid_rTensor_eq_zero z fun f => by
    have := h f
    change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
      ((sectionsBaseChangeEquivOf H F hbij U).symm (Stacks.Tag0CKW.pushforwardSection y))) = 0
      at this
    rwa [← hz, LinearEquiv.symm_apply_apply] at this
  change Stacks.Tag0CKW.pushforwardSection y = 0
  rw [← hz, hz0, map_zero]

omit [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent F] in
/-- **A morphism into `p_* p^* F` is zero as soon as all its traces are.** -/
theorem eq_zero_of_forall_comp_traceOf_eq_zero
    (hfree : letI := baseAlgebra q; Module.Free Γ(S, ⊤) Γ(T, ⊤)) {G : X.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F))
    (h : ∀ f : (letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)),
      φ ≫ traceOf H F hbij f = 0) : φ = 0 := by
  ext U x
  exact eq_zero_of_forall_traceOf_app_eq_zero H F hbij hfree U _ fun f =>
    congrArg (fun m => m.app U x) (h f)

end Detect

end Stacks.FlatTrace

end
