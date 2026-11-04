module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.FlatPullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# Pullback along a jointly surjective family of flat morphisms reflects isomorphisms

Let `{f_i : X_i ⟶ S}` be a family of flat morphisms of schemes whose images cover `S` — in
particular a family lying in `AlgebraicGeometry.Scheme.fpqcPrecoverage S`.  Pullback along the
family then reflects zero objects, monomorphisms, epimorphisms and isomorphisms of **arbitrary**
sheaves of `𝒪_S`-modules, with no quasi-coherence hypothesis anywhere: the stalk of `f_i^* M` at
`x` is the base change of the stalk of `M` at `f_i(x)` along a flat local homomorphism of local
rings, which is faithfully flat, and joint surjectivity makes every point of `S` such an
`f_i(x)`.

The consequence this file exists for is the last line of the chain: if a sheaf of modules `M`
admits a morphism `h : M ⟶ G` to a *quasi-coherent* `G` whose pullback along every member of the
family is an isomorphism, then `M` is itself quasi-coherent
(`Stacks.Descent.isQuasicoherent_of_hom_of_forall_isIso_pullback`).  The descent of
quasi-coherence along an fpqc covering family itself, for an arbitrary sheaf of modules, is
`Stacks.Descent.isQuasicoherent_of_pullback_fpqc` of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcQuasicoherence.lean`.

## Main results

* `Stacks.Descent.isZero_of_forall_isZero_pullback`: a sheaf of modules all of whose pullbacks
  along the family vanish is zero.
* `Stacks.Descent.mono_of_forall_mono_pullback` and
  `Stacks.Descent.epi_of_forall_epi_pullback`: monomorphy and epimorphy descend along the
  family.
* `Stacks.Descent.isIso_of_forall_isIso_pullback`: so does isomorphy.
* `Stacks.Descent.mono_unit_pullbackPushforwardAdjunction`: for a single flat surjection the
  unit `M ⟶ g_* g^* M` is a monomorphism, for an arbitrary sheaf of modules `M`.
* `Stacks.Descent.isQuasicoherent_of_hom_of_forall_isIso_pullback` and
  `Stacks.Descent.isQuasicoherent_of_hom_fpqc`: quasi-coherence of `M` from a comparison
  morphism to a quasi-coherent module.
* `Stacks.Descent.FpqcComparisonMorphism`: the existence of such a comparison morphism for every
  sheaf of modules with quasi-coherent pullbacks along an fpqc covering family, and
  `Stacks.Descent.isQuasicoherent_of_pullback_fpqc_of_comparison`, the passage from it to the
  descent of quasi-coherence.  It holds, as `Stacks.Descent.fpqcComparisonMorphism`.

## Implementation notes

No exactness of pullback is needed for `isZero_of_forall_isZero_pullback`, which is
`Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_stalk_of_isZero_pullback` member by member.
Left exactness of flat pullback (`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`)
enters only to carry a kernel through the pullback; right exactness is unconditional, the
functor being a left adjoint, so the epimorphism statement needs no flatness beyond what the
zero-object statement already uses.

The index type of the family is a free universe parameter, as in
`Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_iff_forall_fpqc`; the one-morphism
statement `mono_unit_pullbackPushforwardAdjunction` instantiates it at `Unit`, which keeps the
declaration's universe parameters to those of its statement.

No `stacks` attribute is placed on anything here: none of these statements is a numbered result
of the source.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 09UG](https://stacks.math.columbia.edu/tag/09UG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Descent

variable {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}

/-! ### Reflection of zero objects, monomorphisms, epimorphisms and isomorphisms -/

/-- **A sheaf of modules whose pullback along every member of a jointly surjective family of
flat morphisms of schemes vanishes is zero.**

A sheaf of modules is zero exactly when all of its stalks are, and the stalk of `M` at a point
in the image of a flat `f i` vanishes as soon as the pullback `f_i^* M` does, by Stacks 0098
together with faithful flatness of a flat local homomorphism of local rings. -/
theorem isZero_of_forall_isZero_pullback (f : ∀ i, X i ⟶ S)
    (hsurj : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) [∀ i, Flat (f i)]
    (M : S.Modules) (hM : ∀ i, IsZero ((Scheme.Modules.pullback (f i)).obj M)) :
    IsZero M := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk M fun s => ?_
  obtain ⟨i, x, rfl⟩ := hsurj s
  exact Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_stalk_of_isZero_pullback
    (f i) M x (hM i)

/-- **Monomorphy descends along a jointly surjective family of flat morphisms.**  Flat pullback
is left exact, so it carries the kernel of `h` to the kernel of `f_i^* h`; a morphism of sheaves
of modules is a monomorphism exactly when its kernel vanishes, and vanishing is reflected by the
family. -/
theorem mono_of_forall_mono_pullback (f : ∀ i, X i ⟶ S)
    (hsurj : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) [∀ i, Flat (f i)]
    {M N : S.Modules} (h : M ⟶ N)
    (hh : ∀ i, Mono ((Scheme.Modules.pullback (f i)).map h)) : Mono h := by
  rw [Preadditive.mono_iff_isZero_kernel]
  refine isZero_of_forall_isZero_pullback f hsurj _ fun i => ?_
  have : PreservesFiniteLimits (Scheme.Modules.pullback (f i)) :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat (f i)
  have := hh i
  refine IsZero.of_iso ?_ (PreservesKernel.iso (Scheme.Modules.pullback (f i)) h)
  rw [← Preadditive.mono_iff_isZero_kernel]
  infer_instance

/-- **Epimorphy descends along a jointly surjective family of flat morphisms.**  Pullback is a
left adjoint, so it carries the cokernel of `h` to the cokernel of `f_i^* h` with no flatness
needed; a morphism of sheaves of modules is an epimorphism exactly when its cokernel vanishes,
and vanishing is reflected by the family. -/
theorem epi_of_forall_epi_pullback (f : ∀ i, X i ⟶ S)
    (hsurj : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) [∀ i, Flat (f i)]
    {M N : S.Modules} (h : M ⟶ N)
    (hh : ∀ i, Epi ((Scheme.Modules.pullback (f i)).map h)) : Epi h := by
  rw [Preadditive.epi_iff_isZero_cokernel]
  refine isZero_of_forall_isZero_pullback f hsurj _ fun i => ?_
  have := hh i
  refine IsZero.of_iso ?_ (PreservesCokernel.iso (Scheme.Modules.pullback (f i)) h)
  rw [← Preadditive.epi_iff_isZero_cokernel]
  infer_instance

/-- **Pullback along a jointly surjective family of flat morphisms of schemes reflects
isomorphisms of sheaves of modules.**  Sheaves of modules on a scheme form an abelian, hence
balanced, category, so this is monomorphy and epimorphy together. -/
theorem isIso_of_forall_isIso_pullback (f : ∀ i, X i ⟶ S)
    (hsurj : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) [∀ i, Flat (f i)]
    {M N : S.Modules} (h : M ⟶ N)
    (hh : ∀ i, IsIso ((Scheme.Modules.pullback (f i)).map h)) : IsIso h := by
  have : Mono h := mono_of_forall_mono_pullback f hsurj h fun i => have := hh i; inferInstance
  have : Epi h := epi_of_forall_epi_pullback f hsurj h fun i => have := hh i; inferInstance
  exact isIso_of_mono_of_epi h

/-- **The unit of the pullback--pushforward adjunction along a flat surjection is a
monomorphism**, for an arbitrary sheaf of modules on the target.

This is the injectivity half of the fpqc sheaf condition, and it is the one half that holds
without quasi-coherence: the triangle identity makes `g^*` of the unit a split monomorphism, and
`g^*` reflects monomorphisms. -/
theorem mono_unit_pullbackPushforwardAdjunction {T : Scheme.{u}} (g : T ⟶ S) [Flat g]
    (hsurj : Function.Surjective g.base) (M : S.Modules) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) := by
  refine mono_of_forall_mono_pullback (X := fun _ : Unit => T) (fun _ => g) ?_ _ fun _ => ?_
  · intro s
    obtain ⟨x, hx⟩ := hsurj s
    exact ⟨(), x, hx⟩
  · have : IsSplitMono ((Scheme.Modules.pullback g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) :=
      ⟨⟨(Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
        ((Scheme.Modules.pullback g).obj M),
        (Scheme.Modules.pullbackPushforwardAdjunction g).left_triangle_components M⟩⟩
    infer_instance

/-! ### Descent of quasi-coherence from a comparison morphism -/

/-- **Quasi-coherence descends along a jointly surjective family of flat morphisms, given a
comparison morphism.**  If `h : M ⟶ G` has quasi-coherent target and `f_i^* h` is an isomorphism
for every member of the family, then `h` is an isomorphism and `M` is quasi-coherent. -/
theorem isQuasicoherent_of_hom_of_forall_isIso_pullback (f : ∀ i, X i ⟶ S)
    (hsurj : ∀ s : S, ∃ i, ∃ x : X i, (f i).base x = s) [∀ i, Flat (f i)]
    {M G : S.Modules} (hG : G.IsQuasicoherent) (h : M ⟶ G)
    (hh : ∀ i, IsIso ((Scheme.Modules.pullback (f i)).map h)) : M.IsQuasicoherent :=
  have : IsIso h := isIso_of_forall_isIso_pullback f hsurj h hh
  isQuasicoherent_of_iso (asIso h).symm hG

/-- **`Stacks.Descent.isQuasicoherent_of_hom_of_forall_isIso_pullback` for an fpqc covering
family.**  The members of a family lying in `AlgebraicGeometry.Scheme.fpqcPrecoverage` are flat
and jointly surjective, which is all the statement asks of them. -/
theorem isQuasicoherent_of_hom_fpqc (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    {M G : S.Modules} (hG : G.IsQuasicoherent) (h : M ⟶ G)
    (hh : ∀ i, IsIso ((Scheme.Modules.pullback (f i)).map h)) : M.IsQuasicoherent := by
  obtain ⟨hsurj, hflat⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp hf.2
  have : ∀ i, Flat (f i) := hflat
  refine isQuasicoherent_of_hom_of_forall_isIso_pullback f (fun s => ?_) hG h hh
  obtain ⟨i, x, hx⟩ := hsurj s
  exact ⟨i, x, hx⟩

/-! ### The comparison morphism -/

/-- **The comparison morphism of fpqc descent of quasi-coherence.**  For every fpqc covering
family `{f_i : X_i ⟶ S}` and every sheaf of `𝒪_S`-modules `M` all of whose pullbacks `f_i^* M`
are quasi-coherent, there is a quasi-coherent `𝒪_S`-module `G` and a morphism `M ⟶ G` whose
pullback along every member of the family is an isomorphism.

`Stacks.Descent.isQuasicoherent_of_pullback_fpqc_of_comparison` derives the descent of
quasi-coherence from it, and it holds, as `Stacks.Descent.fpqcComparisonMorphism`. -/
def FpqcComparisonMorphism : Prop :=
  ∀ {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S),
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S →
    ∀ M : S.Modules, (∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) →
      ∃ (G : S.Modules) (_ : G.IsQuasicoherent) (h : M ⟶ G),
        ∀ i, IsIso ((Scheme.Modules.pullback (f i)).map h)

/-- **Descent of quasi-coherence along an fpqc covering family, from the comparison
morphism.**  This is the hypothesis `hqc` of `Stacks.Descent.isEffective_of_essImage` and
`Stacks.Descent.isEffective_of_essSurj` for an fpqc covering family, derived from
`Stacks.Descent.FpqcComparisonMorphism`. -/
theorem isQuasicoherent_of_pullback_fpqc_of_comparison (hc : FpqcComparisonMorphism.{u, v})
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (M : S.Modules)
    (h : ∀ i, ((Scheme.Modules.pullback (f i)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨G, hG, u, hu⟩ := hc f hf M h
  exact isQuasicoherent_of_hom_fpqc f hf hG u hu

end Stacks.Descent

end
