module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion

/-!
# Morphisms out of the representable sheaf of a disjoint union

Let `T` be an object of the big fppf site of `S` whose underlying scheme is the disjoint union
of the schemes of a family `T' a`, along morphisms `c a : T' a ⟶ T`. The inclusions are open
immersions with pairwise disjoint images covering `T`, so they form an fppf covering family of
monomorphisms with empty pairwise intersections, and the representable sheaf of `T` is the
coproduct of the representable sheaves of the `T' a`. In particular a family of morphisms
`yoneda (T' a) ⟶ X` into an fppf sheaf `X` glues to a morphism `yoneda T ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.sieve_ofArrows_mem_topology_of_iso_sigma`: the inclusions cover.
* `AlgebraicGeometry.Space.exists_desc_yoneda_of_iso_sigma`: the gluing of morphisms into an
  fppf sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {σ : Type u}
  (T' : σ → BigFppfOver B S hS) (T : BigFppfOver B S hS) (c : ∀ a, T' a ⟶ T)
  (e : (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) ≅ (BigFppfOver.toScheme B S hS).obj T)

/-- The inclusions of the summands of a disjoint union are monomorphisms of the site. -/
theorem mono_of_iso_sigma
    (he : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a)) (a : σ) : Mono (c a) := by
  have h := (isOpenImmersion_cover_disjoint_of_iso_sigma e he).1 a
  apply (Over.forget (B.obj hS)).mono_of_mono_map
  apply B.inclusion.mono_of_mono_map
  change Mono ((BigFppfOver.toScheme B S hS).map (c a))
  infer_instance

/-- **The summands of a disjoint union cover it.** -/
theorem sieve_ofArrows_mem_topology_of_iso_sigma
    (he : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a)) :
    Sieve.ofArrows (fun i : ULift.{u + 1} σ => T' i.down) (fun i => c i.down) ∈
      BigFppfOver.topology B S hS T := by
  obtain ⟨hopen, hcov, -⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e he
  let E : PreZeroHypercover.{u + 1} T :=
    { I₀ := ULift.{u + 1} σ
      X i := T' i.down
      f i := c i.down }
  have hF : _root_.AlgebraicGeometry.IsFppfCovering
      ⟨T.left, E.map (Over.forget (B.obj hS))⟩ := by
    let E0 := (E.map (Over.forget (B.obj hS))).map B.inclusion
    have hZ : E0.presieve₀ ∈ Scheme.zariskiPrecoverage ((BigFppfOver.toScheme B S hS).obj T) := by
      change Presieve.ofArrows E0.X E0.f ∈ Scheme.zariskiPrecoverage _
      exact (Scheme.ofArrows_mem_precoverage_iff
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})).2
        ⟨fun x => (hcov x).elim fun a ha => ⟨⟨a⟩, ha⟩, fun a => hopen a.down⟩
    unfold _root_.AlgebraicGeometry.IsFppfCovering
    rw [Precoverage.mem_comap_iff]
    simpa [E0, PreZeroHypercover.presieve₀_map, schemeBelowInclusion, Over.forget,
      Functor.map_comp] using Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hZ
  have heq : Sieve.ofArrows (fun i : ULift.{u + 1} σ => T' i.down) (fun i => c i.down) =
      (Sieve.overEquiv T).symm (Sieve.ofArrows _ (fun i : ULift.{u + 1} σ => (c i.down).left)) := by
    apply (Sieve.overEquiv T).injective
    rw [OrderIso.apply_symm_apply]
    exact Sieve.overEquiv_ofArrows (X := B.obj hS) (Y := T) _ _
  rw [heq]
  apply B.topology.overEquiv_symm_mem_over
  simpa [E, PreZeroHypercover.presieve₀_map, Sieve.functorPushforward_overForget_arrows,
    BigFppfOver.forget] using
    B.generate_mem_topology_of_isFppfCovering (E.map (Over.forget (B.obj hS))) hF

/-- **Gluing morphisms out of the summands of a disjoint union.** Morphisms from the
representable sheaves of the summands into an fppf sheaf `X` glue to a morphism from the
representable sheaf of the disjoint union. -/
theorem exists_desc_yoneda_of_iso_sigma
    (he : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (f : ∀ a, yoneda.obj (T' a) ⟶ X) :
    ∃ g : yoneda.obj T ⟶ X, ∀ a, yoneda.map (c a) ≫ g = f a := by
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let J := BigFppfOver.topology B S hS
  obtain ⟨-, -, hdisj⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e he
  let cf : Cofan (fun i : ULift.{u + 1} σ => T' i.down) := Cofan.mk T fun i => c i.down
  have : ∀ i, Mono (cf.inj i) := fun i => mono_of_iso_sigma B S hS T' T c e he i.down
  have hc := J.isColimitCofanMkYoneda (X := fun i : ULift.{u + 1} σ => T' i.down) (c := cf)
    (sieve_ofArrows_mem_topology_of_iso_sigma B S hS T' T c e he)
    (BigFppfOver.bot_mem_topology_of_isInitial B S hS) (by
      intro i j hij Y a b hab
      have hab' := congrArg (BigFppfOver.toScheme B S hS).map hab
      simp only [Functor.map_comp] at hab'
      have : IsEmpty ((BigFppfOver.toScheme B S hS).obj Y) := by
        refine ⟨fun y => ?_⟩
        refine Set.disjoint_left.1 (hdisj (fun h => hij (ULift.ext h)))
          ⟨(BigFppfOver.toScheme B S hS).map a y, rfl⟩ ?_
        refine ⟨(BigFppfOver.toScheme B S hS).map b y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
        exact congrArg (fun k => k y) hab'.symm
      have : IsEmpty (B.inclusion.obj Y.left) := this
      exact ⟨Over.isInitialOfIsInitialLeft (isInitial_schemeBelow B isInitialOfIsEmpty)⟩)
  let s : Cofan (fun i : ULift.{u + 1} σ => J.yoneda.obj (T' i.down)) :=
    Cofan.mk ⟨X, hX⟩ fun i => ObjectProperty.homMk (f i.down)
  exact ⟨(hc.desc s).hom, fun a => congrArg (fun φ => φ.hom) (hc.fac s ⟨⟨a⟩⟩)⟩

end AlgebraicGeometry.Space

end
