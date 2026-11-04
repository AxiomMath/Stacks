module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.HomologyLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# A quasi-isomorphism of complexes of sheaves of modules, by a chase of local sections

Let `φ : K ⟶ L` be a morphism of cochain complexes of sheaves of modules on a site. If every
cycle of `L` is, locally, the image of a cycle of `K` up to a boundary of `L`, and every cycle of
`K` whose image is a boundary of `L` is, locally, a boundary of `K`, then `φ` is a
quasi-isomorphism.

## Main results

* `SheafOfModules.quasiIso_of_forall_exists_mem_sieve`: the criterion.

## Implementation notes

The two conditions are those of `PresheafOfModules.isLocallySurjective_homologyMap` and
`PresheafOfModules.isLocallyInjective_homologyMap` for the underlying complexes of presheaves of
modules, so their homology presheaves are locally bijective and their sheafifications are
quasi-isomorphic (`PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective`).  A
complex of sheaves is its own sheafification, through the counit
`Stacks.SheafOfModules.EpiMono.counitApp`, which is an isomorphism; transporting along it gives
the statement for `φ` itself.

The degrees adjacent to `n` are named `j` and `k` with `j + 1 = n` and `n + 1 = k`, rather than
written `n - 1` and `n + 1`, so that the criterion can be supplied for complexes whose degrees
are not literally of that form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- Restriction of sections of a sheaf of modules along an identity is the identity. -/
theorem map_id_apply (M : SheafOfModules.{t} R) (U : C) (x : M.val.obj (op U)) :
    M.val.map (𝟙 (op U)) x = x := by
  rw [M.val.map_id]
  rfl

/-- **The sections-chase criterion for a quasi-isomorphism of complexes of sheaves of modules.**
If every cycle of `L` is locally homologous to the image of a cycle of `K`, and every cycle of `K`
whose image is a boundary is locally a boundary, then `φ` is a quasi-isomorphism. -/
theorem quasiIso_of_forall_exists_mem_sieve {K L : CochainComplex (SheafOfModules.{t} R) ℤ}
    (φ : K ⟶ L)
    (hsurj : ∀ (j n k : ℤ), j + 1 = n → n + 1 = k → ∀ (V : C) (z : (L.X n).val.obj (op V)),
      (L.d n k).val.app (op V) z = 0 →
        ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b →
          ∃ z' : (K.X n).val.obj (op W), (K.d n k).val.app (op W) z' = 0 ∧
            ∃ y : (L.X j).val.obj (op W),
              (L.X n).val.map b.op z = (φ.f n).val.app (op W) z' + (L.d j n).val.app (op W) y)
    (hinj : ∀ (j n k : ℤ), j + 1 = n → n + 1 = k → ∀ (V : C) (z' : (K.X n).val.obj (op V)),
      (K.d n k).val.app (op V) z' = 0 → ∀ y : (L.X j).val.obj (op V),
        (φ.f n).val.app (op V) z' = (L.d j n).val.app (op V) y →
        ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b →
          ∃ y' : (K.X j).val.obj (op W),
            (K.X n).val.map b.op z' = (K.d j n).val.app (op W) y') :
    QuasiIso φ := by
  let F := (SheafOfModules.forget.{t} R).mapHomologicalComplex (ComplexShape.up ℤ)
  have hq : QuasiIso (((PresheafOfModules.sheafification.{t} (J := J)
      (𝟙 R.obj)).mapHomologicalComplex (ComplexShape.up ℤ)).map (F.map φ)) :=
    PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective (𝟙 R.obj) (F.map φ)
      (fun n => PresheafOfModules.isLocallyInjective_homologyMap (F.map φ) n
        fun V z' hz' y hy => hinj _ n _ (by simp) (by simp) V z' hz' y hy)
      (fun n => PresheafOfModules.isLocallySurjective_homologyMap (F.map φ) n
        fun V z hz => hsurj _ n _ (by simp) (by simp) V z hz)
  let e : (F ⋙ (PresheafOfModules.sheafification.{t} (J := J) (𝟙 R.obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)) ≅ 𝟭 _ :=
    Functor.mapHomologicalComplexCompIso
      (NatIso.ofComponents
        (F := SheafOfModules.forget.{t} R ⋙
          PresheafOfModules.sheafification.{t} (J := J) (𝟙 R.obj))
        (G := 𝟭 _)
        (fun M => @asIso _ _ _ _ (Stacks.SheafOfModules.EpiMono.counitApp (J := J) M)
          (Stacks.SheafOfModules.EpiMono.isIsoCounitApp (J := J) M))
        Stacks.SheafOfModules.EpiMono.counitApp_naturality) _ ≪≫
      Functor.mapHomologicalComplexIdIso _ _
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso e φ)).1 hq


/-- A section killed by `f` lifts along a kernel `ι` of `f`, since sections are left exact. -/
private theorem exists_section_of_isLimit_kernelFork {C' : Type u'} [Category.{v} C']
    {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{u}} {X M N : SheafOfModules.{t} R'}
    (ι : X ⟶ M) (f : M ⟶ N) (w : ι ≫ f = 0) (hι : IsLimit (KernelFork.ofι ι w)) (U : C'ᵒᵖ)
    (x : M.val.obj U) (hx : f.val.app U x = 0) : ∃ ξ : X.val.obj U, ι.val.app U ξ = x := by
  let E := SheafOfModules.forget.{t} R' ⋙ PresheafOfModules.evaluation R'.obj U
  have hpl : PreservesLimit (parallelPair f 0) E :=
    PreservesFiniteLimits.preservesFiniteLimits _ |>.preservesLimit
  have hzero : E.map ι ≫ E.map f = 0 := by rw [← E.map_comp, w, E.map_zero]
  obtain ⟨ξ, hξ⟩ :=
    (ShortComplex.moduleCat_exact_iff (ShortComplex.mk (E.map ι) (E.map f) hzero)).mp
      (ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hι E)) x hx
  exact ⟨ξ, hξ⟩

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A section killed by a morphism of sheaves of modules is a section of its kernel: taking
sections over an object is left exact. -/
theorem exists_kernel_section {M N : SheafOfModules.{t} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj U) (hx : f.val.app U x = 0) :
    ∃ ξ : (kernel f).val.obj U, (kernel.ι f).val.app U ξ = x :=
  exists_section_of_isLimit_kernelFork _ f (kernel.condition f) (kernelIsKernel f) U x hx

/-- **An epimorphism of sheaves of modules is locally surjective on sections**, in the form of a
covering sieve above which a given section has preimages. -/
theorem exists_mem_sieve_of_epi {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] (U : C)
    (s : N.val.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃W : C⦄ (b : W ⟶ U), S b →
      ∃ x : M.val.obj (op W), f.val.app (op W) x = N.val.map b.op s :=
  ⟨_, (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi f).imageSieve_mem s,
    fun _ _ hb => hb⟩

/-- **Exactness of a short complex of sheaves of modules is local surjectivity onto the
kernel**: a section of the middle term killed by the second map lifts along the first map
after restriction along the arrows of a covering sieve. -/
theorem exists_mem_sieve_of_exact {S : ShortComplex (SheafOfModules.{t} R)} (hS : S.Exact)
    (U : C) (x : S.X₂.val.obj (op U)) (hx : S.g.val.app (op U) x = 0) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃W : C⦄ (b : W ⟶ U), T b →
      ∃ y : S.X₁.val.obj (op W), S.f.val.app (op W) y = S.X₂.val.map b.op x := by
  obtain ⟨ξ, hξ⟩ := exists_kernel_section S.g (op U) x hx
  have : Epi (kernel.lift S.g S.f S.zero) := (S.exact_iff_epi_kernel_lift).1 hS
  obtain ⟨T, hT, hloc⟩ := exists_mem_sieve_of_epi (kernel.lift S.g S.f S.zero) U ξ
  refine ⟨T, hT, fun W b hb => ?_⟩
  obtain ⟨y, hy⟩ := hloc b hb
  refine ⟨y, ?_⟩
  have h1 := congrArg (fun φ => φ.val.app (op W) y) (kernel.lift_ι S.g S.f S.zero)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h1
  rw [← h1, hy, ← hξ]
  exact PresheafOfModules.naturality_apply (kernel.ι S.g).val b.op ξ

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- **Covering sieves compose.**  If a condition on the arrows into `V` holds, above every arrow
of a covering sieve, on the arrows of a covering sieve of its source, then it holds on the arrows
of a covering sieve of `V`. -/
theorem exists_mem_sieve_of_bind {V : C} {P : ∀ ⦃W : C⦄, (W ⟶ V) → Prop} (S : Sieve V)
    (hS : S ∈ J V)
    (h : ∀ ⦃W : C⦄ (b : W ⟶ V), S b → ∃ T : Sieve W, T ∈ J W ∧
      ∀ ⦃W' : C⦄ (b' : W' ⟶ W), T b' → P (b' ≫ b)) :
    ∃ S' : Sieve V, S' ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S' b → P b := by
  choose T hT hP using h
  refine ⟨Sieve.bind S.arrows (fun W b hb => T b hb), J.bind_covering hS (fun W b hb => hT b hb),
    ?_⟩
  rintro W _ ⟨Y, g, f', hf', hg, rfl⟩
  exact hP f' hf' g hg

/-- A section killed by the differential is a cycle: taking sections over an object is left
exact, and the cycles are a kernel of the differential. -/
theorem exists_iCycles_section (K : CochainComplex (SheafOfModules.{t} R) ℤ) (n k : ℤ)
    (hk : n + 1 = k) (U : Cᵒᵖ) (x : (K.X n).val.obj U) (hx : (K.d n k).val.app U x = 0) :
    ∃ ξ : (K.cycles n).val.obj U, (K.iCycles n).val.app U ξ = x := by
  exact exists_section_of_isLimit_kernelFork _ _ (K.iCycles_d n k)
    (K.cyclesIsKernel n k (by simp [hk])) U x hx

/-- **A morphism of complexes of sheaves of modules which is an epimorphism on `n`-th cohomology
is locally surjective on cycles modulo boundaries**: every cycle of the target is, after
restriction along the arrows of a covering sieve, the image of a cycle of the source up to a
boundary. -/
theorem exists_mem_sieve_of_epi_homologyMap {A B : CochainComplex (SheafOfModules.{t} R) ℤ}
    (α : A ⟶ B) (j n k : ℤ) (hj : j + 1 = n) (hk : n + 1 = k)
    [Epi (HomologicalComplex.homologyMap α n)] (V : C) (z : (B.X n).val.obj (op V))
    (hz : (B.d n k).val.app (op V) z = 0) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (b : W ⟶ V), S b →
      ∃ p : (A.X n).val.obj (op W), (A.d n k).val.app (op W) p = 0 ∧
        ∃ y : (B.X j).val.obj (op W),
          (B.X n).val.map b.op z = (α.f n).val.app (op W) p + (B.d j n).val.app (op W) y := by
  obtain ⟨ξ, hξ⟩ := exists_iCycles_section B n k hk (op V) z hz
  have hex : (ShortComplex.mk (B.toCycles j n) (B.homologyπ n)
      (B.toCycles_comp_homologyπ j n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (B.homologyIsCokernel j n (by simp [← hj]))
  obtain ⟨S₁, hS₁, h₁⟩ := exists_mem_sieve_of_epi (HomologicalComplex.homologyMap α n) V
    ((B.homologyπ n).val.app (op V) ξ)
  refine exists_mem_sieve_of_bind S₁ hS₁ (fun W b hb => ?_)
  obtain ⟨η, hη⟩ := h₁ b hb
  obtain ⟨S₂, hS₂, h₂⟩ := exists_mem_sieve_of_epi (A.homologyπ n) W η
  refine exists_mem_sieve_of_bind S₂ hS₂ (fun W' b' hb' => ?_)
  obtain ⟨ζ, hζ⟩ := h₂ b' hb'
  let r : (B.cycles n).val.obj (op W') := (B.cycles n).val.map (b' ≫ b).op ξ
  set ζ' : (B.cycles n).val.obj (op W') :=
    (HomologicalComplex.cyclesMap α n).val.app (op W') ζ - r with hζ'
  have hπ : (B.homologyπ n).val.app (op W') ζ' = 0 := by
    have e1 : (B.homologyπ n).val.app (op W')
        ((HomologicalComplex.cyclesMap α n).val.app (op W') ζ) =
        (HomologicalComplex.homologyMap α n).val.app (op W')
          ((A.homologyπ n).val.app (op W') ζ) := by
      rw [← comp_val_app_apply, ← comp_val_app_apply, HomologicalComplex.homologyπ_naturality]
    have e2 : (B.homologyπ n).val.app (op W') r =
        (B.homology n).val.map (b' ≫ b).op ((B.homologyπ n).val.app (op V) ξ) :=
      PresheafOfModules.naturality_apply (B.homologyπ n).val (b' ≫ b).op ξ
    have e3 : (HomologicalComplex.homologyMap α n).val.app (op W')
        ((A.homology n).val.map b'.op η) =
        (B.homology n).val.map b'.op ((HomologicalComplex.homologyMap α n).val.app (op W) η) :=
      PresheafOfModules.naturality_apply (HomologicalComplex.homologyMap α n).val b'.op η
    rw [hζ', map_sub, e1, e2, hζ, e3, hη, ← PresheafOfModules.map_comp_apply]
    exact sub_self _
  obtain ⟨S₃, hS₃, h₃⟩ := exists_mem_sieve_of_exact hex W' ζ' hπ
  refine ⟨S₃, hS₃, fun W'' b'' hb'' => ?_⟩
  obtain ⟨y, hy⟩ := h₃ b'' hb''
  obtain ⟨ζr, hζr⟩ : ∃ x : (A.cycles n).val.obj (op W''), x = (A.cycles n).val.map b''.op ζ :=
    ⟨_, rfl⟩
  obtain ⟨ξr, hξr⟩ : ∃ x : (B.cycles n).val.obj (op W''),
      x = (B.cycles n).val.map ((b'' ≫ b') ≫ b).op ξ := ⟨_, rfl⟩
  refine ⟨(A.iCycles n).val.app (op W'') ζr, ?_, -y, ?_⟩
  · rw [← comp_val_app_apply, A.iCycles_d, zero_val_app_apply]
  · change (B.toCycles j n).val.app (op W'') y = (B.cycles n).val.map b''.op ζ' at hy
    have hd : (B.d j n).val.app (op W'') y =
        (B.iCycles n).val.app (op W'') ((B.toCycles j n).val.app (op W'') y) := by
      rw [← comp_val_app_apply, HomologicalComplex.toCycles_i]
    have hα : (α.f n).val.app (op W'') ((A.iCycles n).val.app (op W'') ζr) =
        (B.iCycles n).val.app (op W'')
          ((HomologicalComplex.cyclesMap α n).val.app (op W'') ζr) := by
      rw [← comp_val_app_apply, ← comp_val_app_apply, HomologicalComplex.cyclesMap_i]
    have hz' : (B.X n).val.map ((b'' ≫ b') ≫ b).op z = (B.iCycles n).val.app (op W'') ξr := by
      rw [← hξ, hξr]
      exact (PresheafOfModules.naturality_apply (B.iCycles n).val ((b'' ≫ b') ≫ b).op ξ).symm
    have hy' : (B.cycles n).val.map b''.op ζ' =
        (HomologicalComplex.cyclesMap α n).val.app (op W'') ζr - ξr := by
      rw [hζ', map_sub, hζr, hξr, PresheafOfModules.naturality_apply, Category.assoc,
        op_comp (f := b'') (g := b' ≫ b),
        PresheafOfModules.map_comp_apply (B.cycles n).val (b' ≫ b).op b''.op ξ]
      rfl
    rw [map_neg, hd, hy, hy', hα, hz', map_sub]
    abel

end SheafOfModules
