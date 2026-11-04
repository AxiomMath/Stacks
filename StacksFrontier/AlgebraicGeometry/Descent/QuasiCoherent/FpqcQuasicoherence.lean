module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FlatFamilyReflection
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.StandardFpqcRefinement
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# Quasi-coherence descends along an fpqc covering

Let `{f_i : X_i ⟶ S}` be an fpqc covering family and let `M` be an arbitrary sheaf of
`𝒪_S`-modules. If every pullback `f_i^* M` is quasi-coherent, then so is `M`.

The proof reduces to a single faithfully flat morphism of affine schemes `g = Spec.map φ`. For
an arbitrary sheaf of modules `M` the unit `η_M : M ⟶ g_* g^* M` identifies `M` with the kernel
of `η_{g_* g^* M} - g_* g^* η_M`: after pullback along `g` the pair splits by the counit of the
adjunction, `g^*` preserves the kernel because `g` is flat, and `g^*` reflects isomorphisms
because `g` is flat and surjective. When `g^* M` is quasi-coherent both terms of the pair are
pushforwards of quasi-coherent modules along a morphism of affine schemes, hence quasi-coherent,
and so is the kernel.

The general case is Zariski-local on `S`: over an affine open `V` of `S` the covering is refined
by the standard fpqc covering of Stacks 022E, a finite family of morphisms `Spec (A k) ⟶ V`
through affine opens of the members, whose product of global sections is faithfully flat over
`Γ(V, 𝒪)`; and on the spectrum of the product, quasi-coherence is again checked on the open
cover by the factors.

## Main results

* `Stacks.Descent.isIso_kernelLift_unit`: the equalizer presentation of an arbitrary sheaf of
  modules along a flat surjective morphism of schemes.
* `Stacks.Descent.isQuasicoherent_of_pullback_specMap`: quasi-coherence descends along
  `Spec.map φ` for a faithfully flat ring map `φ`.
* `Stacks.Descent.isQuasicoherent_of_pullback_fpqc`: quasi-coherence descends along an fpqc
  covering family.
* `Stacks.Descent.fpqcComparisonMorphism`: `Stacks.Descent.FpqcComparisonMorphism` holds.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Descent

/-! ### The affine case -/

section Affine

/-- The difference `η_{g_* g^* M} - g_* g^* η_M : g_* g^* M ⟶ g_* g^* g_* g^* M` of the two
maps of the equalizer presentation of `M` along `g`, `η` the unit of `g^* ⊣ g_*`. -/
def unitDiff {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules) :
    (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))) :=
  let A := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)
  let B := (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj A)
  let a : A ⟶ B := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app A
  let b : A ⟶ B := (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M))
  a - b

/-- The unit `η_M : M ⟶ g_* g^* M` composed with `Stacks.Descent.unitDiff g M` is zero. -/
lemma unit_comp_unitDiff {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫ unitDiff g M = 0 := by
  rw [unitDiff, Preadditive.comp_sub, sub_eq_zero]
  exact (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)

/-- **The equalizer presentation of a sheaf of modules along a flat surjective morphism.** Let
`g : T ⟶ S` be flat and surjective and `M` an `𝒪_S`-module, with `η` the unit of `g^* ⊣ g_*`.
Then the morphism from `M` to the kernel of `η_{g_* g^* M} - g_* g^* η_M` induced by `η_M` is an
isomorphism, for an arbitrary sheaf of modules `M`. -/
theorem isIso_kernelLift_unit {T S : Scheme.{u}} (g : T ⟶ S) [Flat g]
    (hg : Function.Surjective g.base) (M : S.Modules) :
    IsIso (kernel.lift (unitDiff g M) ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
      (unit_comp_unitDiff g M)) := by
  have := AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat g
  refine isIso_of_forall_isIso_pullback (X := fun _ : Unit => T) (fun _ => g)
    (fun s => let ⟨x, hx⟩ := hg s; ⟨(), x, hx⟩) _ fun _ => ?_
  have h0 : kernel.ι (unitDiff g M) ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) =
      kernel.ι (unitDiff g M) ≫ (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) := by
    rw [← sub_eq_zero, ← Preadditive.comp_sub]
    exact kernel.condition (unitDiff g M)
  have hsplit : (Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M)) =
      (Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) := by
    calc (Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M))
        = (Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M) ≫
            (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))) ≫
            (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
              ((Scheme.Modules.pullback g).obj
                ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))) := by
          rw [Functor.map_comp, Category.assoc,
            (Scheme.Modules.pullbackPushforwardAdjunction g).left_triangle_components,
            Category.comp_id]
      _ = _ := by
          rw [h0, Functor.map_comp, Category.assoc]
          congr 1
          exact (Scheme.Modules.pullbackPushforwardAdjunction g).counit.naturality
            ((Scheme.Modules.pullback g).map
              ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M))
  refine ⟨⟨(Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M)) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
        ((Scheme.Modules.pullback g).obj M), ?_, ?_⟩⟩
  · rw [← Functor.map_comp_assoc, kernel.lift_ι]
    exact (Scheme.Modules.pullbackPushforwardAdjunction g).left_triangle_components M
  · rw [← cancel_mono ((Scheme.Modules.pullback g).map (kernel.ι (unitDiff g M))),
      Category.assoc, Category.assoc, ← Functor.map_comp, kernel.lift_ι, Category.id_comp]
    exact hsplit.symm

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Quasi-coherence descends along a faithfully flat morphism of affine schemes.** For a
faithfully flat ring map `φ : R ⟶ S`, an arbitrary sheaf of modules `M` on `Spec R` is
quasi-coherent as soon as its pullback along `Spec.map φ` is. -/
theorem isQuasicoherent_of_pullback_specMap (hφ : φ.hom.FaithfullyFlat) (M : (Spec R).Modules)
    (hM : ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨hfl, hsurj⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  have h := isIso_kernelLift_unit (Spec.map φ) hsurj.surj M
  have : ((Scheme.Modules.pushforward (Spec.map φ)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap φ _
  have : ((Scheme.Modules.pushforward (Spec.map φ)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M)))).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap φ _
  exact isQuasicoherent_of_iso (asIso (kernel.lift (unitDiff (Spec.map φ) M)
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)
    (unit_comp_unitDiff (Spec.map φ) M))).symm inferInstance

end Affine

/-! ### Fpqc coverings -/

section Fpqc

/-- Quasi-coherence of a pullback is unchanged when the morphism is rewritten as a composite. -/
lemma isQuasicoherent_pullback_of_comp_eq {Z Y S : Scheme.{u}} {p : Z ⟶ Y} {q : Y ⟶ S}
    {r : Z ⟶ S} (hr : p ≫ q = r) (M : S.Modules)
    (h : ((Scheme.Modules.pullback q).obj M).IsQuasicoherent) :
    ((Scheme.Modules.pullback r).obj M).IsQuasicoherent :=
  isQuasicoherent_of_iso ((Scheme.Modules.pullbackComp p q).app M ≪≫
    (Scheme.Modules.pullbackCongr hr).app M) (Stacks.Modules.isQuasicoherent_pullback p _ h)

/-- A jointly surjective family of open immersions has open images covering the target. -/
lemma iSup_opensRange_eq_top {S : Scheme.{u}} {I : Type*} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) : ⨆ i, (f i).opensRange = ⊤ :=
  eq_top_iff.2 fun s _ => by
    obtain ⟨i, x, hx⟩ := hf s
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, x, hx⟩

/-- Quasi-coherence descends along a Zariski covering given by an `ofArrows` presieve. -/
private lemma isQuasicoherent_of_pullback_ofArrows_zariski {S : Scheme.{u}} {I : Type*}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage.{u} S) (M : S.Modules)
    (h : ∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) : M.IsQuasicoherent := by
  rw [Scheme.ofArrows_mem_precoverage_iff] at hf
  have := hf.2
  exact isQuasicoherent_of_pullback_zariski f (iSup_opensRange_eq_top f hf.1) M h

/-- **Quasi-coherence descends along an fpqc covering family.** Let `{f_i : X_i ⟶ S}` be an fpqc
covering family and `M` an arbitrary sheaf of `𝒪_S`-modules. If every pullback `f_i^* M` is
quasi-coherent, then `M` is quasi-coherent. -/
theorem isQuasicoherent_of_pullback_fpqc {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (M : S.Modules) (h : ∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  refine isQuasicoherent_of_pullback_ofArrows_zariski
    (ofArrows_affineOpens_mem_zariskiPrecoverage S) M fun V => ?_
  obtain ⟨n, A, g, a, t, hflat, hcov, hopen, hcomm, hff⟩ :=
    exists_standardFpqcCovering_over_affineOpen (⟨I, X, f⟩ : PreZeroHypercover S) hf V
  have hV : IsAffine V.1.toScheme := V.2
  refine isQuasicoherent_of_pullback_specMap (piAppTopHom g) hff _ ?_
  refine isQuasicoherent_of_pullback_ofArrows_zariski
    (ofArrows_specPiEval_mem_zariskiPrecoverage (fun j ↦ Γ(Spec (A j), ⊤))) _ fun k => ?_
  have hk : ((Spec (A k)).isoSpec.inv ≫ t k) ≫ f (a k) =
      (specPiEval (fun j ↦ Γ(Spec (A j), ⊤)) k ≫ Spec.map (piAppTopHom g)) ≫
        V.1.toScheme.isoSpec.inv ≫ V.1.ι := by
    simp [hcomm, specPiEval_comp_specMap_piAppTopHom_assoc]
  exact isQuasicoherent_of_iso
    ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M).symm
    (isQuasicoherent_pullback_of_comp_eq hk M (h (a k)))

/-- **`Stacks.Descent.FpqcComparisonMorphism` holds**: for a sheaf of modules all of whose
pullbacks along an fpqc covering family are quasi-coherent, the identity is a comparison morphism
to a quasi-coherent module, `M` itself being quasi-coherent by
`Stacks.Descent.isQuasicoherent_of_pullback_fpqc`. -/
theorem fpqcComparisonMorphism : FpqcComparisonMorphism.{u, v} :=
  fun f hf M h => ⟨M, isQuasicoherent_of_pullback_fpqc f hf M h, 𝟙 M, fun _ => inferInstance⟩

end Fpqc

end Stacks.Descent

end
