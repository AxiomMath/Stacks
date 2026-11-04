module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Defs
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# Continuous maps into the discrete rings of functions form an fppf sheaf

Let `S` be a scheme of a big fppf site and let `E` be a topological ring. On the affine objects
`T` of the site, the presheaf

`T ↦ {continuous ring maps E ⟶ Γ(T, 𝒪_T)}`,

with `Γ(T, 𝒪_T)` discrete, is a sheaf for the fppf topology of the big affine site. The ring
maps glue because global functions satisfy fpqc descent (Stacks 023M, through the sheaf property
of `𝒪` on the big fpqc site, Stacks 03OG); the glued map is continuous because a covering sieve
of an affine object contains a *finite* covering family, so the kernel of the glued map is a
finite intersection of open ideals.

This is the sheaf property behind the sheaf property of the structure sheaf of a formal
algebraic space: maps from `E` into the ring of functions of a sheaf are natural families of
such maps (`AlgebraicGeometry.FormalSpace.ringOfFunctionsHomEquiv`).

## Main results

* `AlgebraicGeometry.FormalSpace.isSheaf_globalSections_bigAffineFppf`: global functions are a
  sheaf of types on the big affine fppf site.
* `AlgebraicGeometry.FormalSpace.isSheaf_discreteFunctions_comp_coyoneda`: the presheaf of
  continuous ring maps `E ⟶ Γ(T, 𝒪_T)` is a sheaf on the big affine fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of types of global functions on the affine objects of the big fppf site. -/
abbrev globalSectionsBigAffine : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u :=
  (BigAffineFppf.inclusion B S hS ⋙ Over.post (X := B.obj hS) B.inclusion).op ⋙
    Stacks.Sites.globalSectionsOver S

/-- Global functions are a sheaf of types on the big affine fppf site: they are an fpqc sheaf
(Stacks 03OG), and an fpqc sheaf restricts to a sheaf on the big affine fppf site
(Stacks 03O4). -/
theorem isSheaf_globalSections_bigAffineFppf :
    Presieve.IsSheaf (BigAffineFppf.topology B S hS) (globalSectionsBigAffine B S hS) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp <|
    isSheaf_bigAffineFppf_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S)

variable {B S hS}

/-- The restriction of global functions along a morphism of affine objects, as a ring
homomorphism. -/
noncomputable abbrev restrictFunctions {T T' : BigAffineFppf B S hS} (t : T' ⟶ T) :
    Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤) →+* Γ((BigAffineFppf.toScheme B S hS).obj T', ⊤) :=
  (Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map t).op).hom

/-- The restriction map of `globalSectionsBigAffine` along `t` is `restrictFunctions t`. -/
theorem globalSectionsBigAffine_map_apply {T T' : BigAffineFppf B S hS} (t : T' ⟶ T)
    (a : Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤)) :
    (globalSectionsBigAffine B S hS).map t.op a = restrictFunctions t a :=
  rfl

/-- The restriction map of `discreteFunctions` along `t` is `restrictFunctions t` on the
underlying functions. -/
theorem discreteFunctions_map_apply {T T' : BigAffineFppf B S hS} (t : T' ⟶ T)
    (a : (discreteFunctions B S hS).obj (op T)) :
    (discreteFunctions B S hS).map t.op a = ULift.up (restrictFunctions t a.down) :=
  rfl

/-- A ring map into the global functions of an affine object, as a ring map into the discrete
ring of functions. -/
noncomputable def toDiscreteFunctions {E : Type*} [Ring E] (T : BigAffineFppf B S hS)
    (φ : E →+* Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤)) :
    E →+* (discreteFunctions B S hS).obj (op T) where
  toFun e := ULift.up (φ e)
  map_one' := congrArg ULift.up (map_one φ)
  map_mul' a b := congrArg ULift.up (map_mul φ a b)
  map_zero' := congrArg ULift.up (map_zero φ)
  map_add' a b := congrArg ULift.up (map_add φ a b)

/-- The underlying function of `toDiscreteFunctions T φ e` is `φ e`. -/
@[simp]
theorem toDiscreteFunctions_apply_down {E : Type*} [Ring E] (T : BigAffineFppf B S hS)
    (φ : E →+* Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤)) (e : E) :
    (toDiscreteFunctions T φ e).down = φ e :=
  rfl

/-- **Continuous ring maps into the discrete rings of functions form a sheaf on the big affine
fppf site.** For a topological ring `E`, the presheaf `T ↦ (E ⟶ Γ(T, 𝒪_T))` of continuous ring
maps into the discrete ring of global functions satisfies the sheaf condition for every covering
sieve of the big affine fppf site. -/
theorem isSheaf_discreteFunctions_comp_coyoneda (E : TopCommRingCat.{u + 1}) :
    Presieve.IsSheaf (BigAffineFppf.topology B S hS)
      (discreteFunctions B S hS ⋙ coyoneda.obj (op E)) := by
  intro T R hR
  have hΓ := (isSheaf_globalSections_bigAffineFppf B S hS) R hR
  obtain ⟨V, hfin, -, hVcov, hVle⟩ := Stacks.Sites.exists_finite_flat_covering_refinement
    (BigAffineFppf.toScheme B S hS) (BigAffineFppf.precoverage B S hS)
    (fun R hR => BigAffineFppf.finite_flat_of_mem_siteKindPrecoverage B S hS .fppf R hR) R hR
  have hVsep := ((isSheaf_globalSections_bigAffineFppf B S hS) V.sieve₀ hVcov).isSeparatedFor
  intro x hx
  let xm : ∀ {T' : BigAffineFppf B S hS} (t : T' ⟶ T), R t →
      (E ⟶ (discreteFunctions B S hS).obj (op T')) := fun t ht => x t ht
  let r : ∀ {T' : BigAffineFppf B S hS} (t : T' ⟶ T), R t →
      (E →+* Γ((BigAffineFppf.toScheme B S hS).obj T', ⊤)) :=
    fun t ht => ULift.ringEquiv.toRingHom.comp (xm t ht).1
  have hxm : ∀ {T' T'' : BigAffineFppf B S hS} (t : T' ⟶ T) (t' : T'' ⟶ T') (ht : R t) (e : E),
      r (t' ≫ t) (R.downward_closed ht t') e = restrictFunctions t' (r t ht e) :=
    fun t t' ht e => congrArg (fun g : E ⟶ (discreteFunctions B S hS).obj (op _) => (g e).down)
      ((Presieve.compatible_iff_sieveCompatible x).mp hx t t' ht)
  let y : E → Presieve.FamilyOfElements (globalSectionsBigAffine B S hS) R.arrows :=
    fun e _ t ht => r t ht e
  have hy : ∀ e, (y e).Compatible := fun e => by
    rw [Presieve.compatible_iff_sieveCompatible]
    exact fun _ _ t t' ht => hxm t t' ht e
  let s : E → Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤) := fun e => hΓ.amalgamate (y e) (hy e)
  have hs : ∀ (e : E) {T' : BigAffineFppf B S hS} (t : T' ⟶ T) (ht : R t),
      restrictFunctions t (s e) = r t ht e :=
    fun e _ t ht => hΓ.valid_glue (hy e) t ht
  have hsep : ∀ a b : Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤),
      (∀ (T' : BigAffineFppf B S hS) (t : T' ⟶ T), R t →
        restrictFunctions t a = restrictFunctions t b) → a = b :=
    fun a b h => hΓ.isSeparatedFor.ext fun T' t ht => h T' t ht
  let φ : E →+* Γ((BigAffineFppf.toScheme B S hS).obj T, ⊤) :=
    { toFun := s
      map_one' := hsep _ _ fun T' t ht => by simp [hs _ t ht]
      map_mul' := fun a b => hsep _ _ fun T' t ht => by simp [hs _ t ht]
      map_zero' := hsep _ _ fun T' t ht => by simp [hs _ t ht]
      map_add' := fun a b => hsep _ _ fun T' t ht => by simp [hs _ t ht] }
  have hVR : ∀ i, R (V.f i) := fun i => hVle _ (Sieve.ofArrows_mk _ _ i)
  have hker : ∀ e : E, (∀ i, (xm (V.f i) (hVR i) e) = 0) → φ e = 0 := by
    intro e he
    refine hVsep.ext fun T' t ht => ?_
    obtain ⟨T'', a, b, ⟨i⟩, rfl⟩ := ht
    change restrictFunctions (a ≫ V.f i) (s e) = restrictFunctions (a ≫ V.f i) 0
    rw [map_zero, hs e _ (R.downward_closed (hVR i) a), hxm (V.f i) a (hVR i),
      show r (V.f i) (hVR i) e = 0 from congrArg ULift.down (he i), map_zero]
  have hφcont : Continuous (toDiscreteFunctions T φ) := by
    refine continuous_of_continuousAt_zero _ ?_
    rw [ContinuousAt, map_zero, nhds_discrete ((discreteFunctions B S hS).obj (op T)),
      Filter.tendsto_pure]
    have _ : Finite V.I₀ := hfin
    have hopen : ∀ i, {e : E | (xm (V.f i) (hVR i) e) = 0} ∈ 𝓝 (0 : E) :=
      fun i => ((xm _ _).2.isOpen_preimage {0} (isOpen_discrete _)).mem_nhds (by
        show (xm _ _) 0 = 0
        exact map_zero (xm _ _).1)
    filter_upwards [Filter.iInter_mem.mpr hopen] with e he
    rw [Set.mem_iInter] at he
    show ULift.up (φ e) = 0
    rw [hker e he]
    rfl
  let σ : E ⟶ (discreteFunctions B S hS).obj (op T) :=
    ⟨toDiscreteFunctions T φ, hφcont⟩
  refine ⟨σ, fun T' t ht => ?_, fun σ' hσ' => ?_⟩
  · exact Subtype.ext (RingHom.ext fun e => ULift.ext _ _ (hs e t ht))
  · refine Subtype.ext (RingHom.ext fun e => ULift.ext _ _ (hsep _ _ fun T' t ht => ?_))
    exact (congrArg (fun g : E ⟶ (discreteFunctions B S hS).obj (op T') => (g e).down)
      (hσ' t ht)).trans (hs e t ht).symm

end AlgebraicGeometry.FormalSpace

end
