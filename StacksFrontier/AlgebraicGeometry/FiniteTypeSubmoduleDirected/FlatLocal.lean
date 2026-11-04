module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcEffective023T
import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmoduleDirected.Capture
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Inclusion of quasi-coherent submodules is fpqc local

Let `F` be a quasi-coherent module on a scheme `X` and `N, N' ⊆ F` two quasi-coherent
submodules. If `{q i : T i ⟶ X}` is an fpqc covering family (for instance a jointly surjective
family of étale morphisms) and, for every `i`, the image of `q i ^* N` in `q i ^* F` lies in the
image of `q i ^* N'`, then `N ≤ N'`.

This is the descent of the inclusion relation along a faithfully flat covering, and it is the
check by which, on a quasi-compact quasi-separated algebraic space, a finite type quasi-coherent
submodule built by gluing is compared with a prescribed one on an étale chart (the module form of
[Stacks, Tag 0829], proved along [Stacks, Tag 08GP]).

## Main results

* `Stacks.FiniteTypeSubmodule.comp_eq_zero_of_ofHom_le`: if the local image of `g` lies in the
  local image of `h`, every morphism killing `h` kills `g`.
* `Stacks.FiniteTypeSubmodule.ofHom_pullback_le_of_le`: pullback preserves the inclusion of
  submodules, read through the local images of the pulled back inclusions.
* `Stacks.FiniteTypeSubmodule.le_of_forall_ofHom_pullback_le`: **the descent of an inclusion**
  along an fpqc covering family.
* `Stacks.FiniteTypeSubmodule.le_iff_forall_ofHom_pullback_le`: the same as an equivalence.
* `Stacks.FiniteTypeSubmodule.le_of_forall_ofHom_pullback_le_of_mem_etalePrecoverage` and
  `Stacks.FiniteTypeSubmodule.le_of_ofHom_pullback_le`: the cases of an étale covering family
  and of a single surjective flat quasi-compact morphism.

## Implementation notes

`N ≤ N'` is equivalent to the vanishing of the composite `N ⟶ F ⟶ F / N'`, because the inclusion
of `N'` is a kernel of its cokernel. Both `N` and `F / N'` are quasi-coherent
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`), so the composite
vanishes as soon as its pullbacks along the covering do, by the separatedness half of fpqc
descent for quasi-coherent modules, `Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc`. Its pullback
along `q i` is `q i ^* N ⟶ q i ^* F ⟶ q i ^* (F / N')`, whose second arrow kills the image of
`q i ^* N'`. No exactness of the pullback is needed: the hypothesis is about local images in
`q i ^* F`, and a morphism killing a map kills everything locally in its image.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SubmodulePrimitives

universe v u

namespace Stacks.FiniteTypeSubmodule

/-! ### Morphisms killing a local image -/

section LocalImage

variable {T : Scheme.{u}}

/-- **A morphism killing `h` kills everything locally in the image of `h`.** If the local image
of `g` lies in the local image of `h` and `h ≫ c = 0`, then `g ≫ c = 0`: a section of the source
of `g` maps, locally, to the image of a section of the source of `h`, which `c` kills, and the
target of `c` is a sheaf. -/
theorem comp_eq_zero_of_ofHom_le {A B F G : T.Modules} (g : A ⟶ F) (h : B ⟶ F) (c : F ⟶ G)
    (hle : ofHom g ≤ ofHom h) (hc : h ≫ c = 0) : g ≫ c = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  rw [Scheme.Modules.Hom.zero_app]
  ext s
  show c.app U (g.app U s) = 0
  have hle' := PresheafOfModules.Submodule.le_iff.1 (SheafOfModules.Submodule.le_iff.1 hle)
  have hmem : g.app U s ∈ (ofHom h).obj (op U) := hle' (op U) (le_obj_ofHom g U ⟨s, rfl⟩)
  choose V hVU hxV t ht using fun x : {x : T // x ∈ U} => (mem_ofHom_iff h _).1 hmem x.1 x.2
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  refine (Stacks.AlgebraicGeometry.CardinalGeneration.asSheaf G).eq_of_locally_eq' V U
    (fun i => homOfLE (hVU i)) hcover _ _ fun i => ?_
  show G.presheaf.map (homOfLE (hVU i)).op (c.app U (g.app U s)) =
    G.presheaf.map (homOfLE (hVU i)).op 0
  rw [map_zero, ← Stacks.AlgebraicGeometry.CardinalGeneration.app_map, ← ht i]
  show ((h ≫ c).app (V i)) (t i) = 0
  rw [hc]
  rfl

end LocalImage

/-! ### Descent of the inclusion of submodules -/

section Descent

variable {X : Scheme.{u}} {F : X.Modules}

/-- **Pullback preserves the inclusion of submodules**, read through the local images of the
pulled back inclusions: if `N ≤ N'`, then for every morphism `q : T ⟶ X` the image of `q^*N` in
`q^*F` lies in the image of `q^*N'`. -/
theorem ofHom_pullback_le_of_le {T : Scheme.{u}} (q : T ⟶ X) {N N' : F.Submodule}
    (h : N ≤ N') :
    ofHom ((Scheme.Modules.pullback q).map (inclusion N)) ≤
      ofHom ((Scheme.Modules.pullback q).map (inclusion N')) := by
  have e : (Scheme.Modules.pullback q).map (inclusion N) =
      (Scheme.Modules.pullback q).map (inclusionOfLE h) ≫
        (Scheme.Modules.pullback q).map (inclusion N') :=
    (congrArg (Scheme.Modules.pullback q).map (inclusionOfLE_inclusion h)).symm.trans
      ((Scheme.Modules.pullback q).map_comp _ _)
  rw [e]
  exact ofHom_comp_le _ _

/-- **A morphism into a quasi-coherent module factors through the cokernel test fpqc
locally.** Let `g : A ⟶ F` and `f : B ⟶ F` be morphisms of quasi-coherent modules on `X` and
`{q i}` an fpqc covering family. If for every `i` the image of `q i ^* g` lies in the image of
`q i ^* f`, then `g` composed with the cokernel of `f` vanishes. -/
theorem comp_cokernel_π_eq_zero_of_forall_ofHom_pullback_le {ι : Type v} {T : ι → Scheme.{u}}
    (q : ∀ i, T i ⟶ X) (hq : Presieve.ofArrows T q ∈ Scheme.fpqcPrecoverage.{u} X)
    {A B G : X.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] [G.IsQuasicoherent]
    (g : A ⟶ G) (f : B ⟶ G)
    (h : ∀ i, ofHom ((Scheme.Modules.pullback (q i)).map g) ≤
      ofHom ((Scheme.Modules.pullback (q i)).map f)) :
    g ≫ cokernel.π f = 0 := by
  refine Stacks.Descent.hom_ext_of_pullback_map_eq_fpqc q hq fun i => ?_
  rw [Functor.map_zero, Functor.map_comp]
  refine comp_eq_zero_of_ofHom_le _ _ _ (h i) ?_
  rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]

/-- **The inclusion of quasi-coherent submodules descends along an fpqc covering.** Let `F` be a
quasi-coherent module on a scheme `X`, `N, N' ⊆ F` quasi-coherent submodules and `{q i}` an fpqc
covering family of `X`. If for every `i` the image of `q i ^* N` in `q i ^* F` lies in the image
of `q i ^* N'`, then `N ≤ N'`. -/
theorem le_of_forall_ofHom_pullback_le {ι : Type v} {T : ι → Scheme.{u}} (q : ∀ i, T i ⟶ X)
    (hq : Presieve.ofArrows T q ∈ Scheme.fpqcPrecoverage.{u} X) [F.IsQuasicoherent]
    (N N' : F.Submodule) (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hN' : (N'.toSheafOfModules : X.Modules).IsQuasicoherent)
    (h : ∀ i, ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N)) ≤
      ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N'))) :
    N ≤ N' := by
  have : (N.toSheafOfModules : X.Modules).IsQuasicoherent := hN
  have : (N'.toSheafOfModules : X.Modules).IsQuasicoherent := hN'
  have h0 := comp_cokernel_π_eq_zero_of_forall_ofHom_pullback_le q hq (inclusion N)
    (inclusion N') h
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift'
    (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (inclusion N'))) (inclusion N) h0
  have hk' : k ≫ inclusion N' = inclusion N := hk
  refine SheafOfModules.Submodule.le_iff.2 (PresheafOfModules.Submodule.le_iff.2 ?_)
  rintro ⟨U⟩ s hs
  have e : ((k ≫ inclusion N').app U) ⟨s, hs⟩ = s := by
    rw [hk']
    rfl
  rw [← e]
  exact ((k.app U) ⟨s, hs⟩).2

/-- **The inclusion of quasi-coherent submodules is fpqc local**: for an fpqc covering family
`{q i}` of `X`, `N ≤ N'` holds exactly when, for every `i`, the image of `q i ^* N` in
`q i ^* F` lies in the image of `q i ^* N'`. -/
theorem le_iff_forall_ofHom_pullback_le {ι : Type v} {T : ι → Scheme.{u}} (q : ∀ i, T i ⟶ X)
    (hq : Presieve.ofArrows T q ∈ Scheme.fpqcPrecoverage.{u} X) [F.IsQuasicoherent]
    (N N' : F.Submodule) (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hN' : (N'.toSheafOfModules : X.Modules).IsQuasicoherent) :
    N ≤ N' ↔ ∀ i, ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N)) ≤
      ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N')) :=
  ⟨fun h i => ofHom_pullback_le_of_le (q i) h, le_of_forall_ofHom_pullback_le q hq N N' hN hN'⟩

/-- **The inclusion of quasi-coherent submodules is étale local**: the case of
`Stacks.FiniteTypeSubmodule.le_of_forall_ofHom_pullback_le` for an étale covering family, which
is an fpqc covering family because étale morphisms are flat and open. -/
theorem le_of_forall_ofHom_pullback_le_of_mem_etalePrecoverage {ι : Type v}
    {T : ι → Scheme.{u}} (q : ∀ i, T i ⟶ X)
    (hq : Presieve.ofArrows T q ∈ Scheme.etalePrecoverage X) [F.IsQuasicoherent]
    (N N' : F.Submodule) (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hN' : (N'.toSheafOfModules : X.Modules).IsQuasicoherent)
    (h : ∀ i, ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N)) ≤
      ofHom ((Scheme.Modules.pullback (q i)).map (inclusion N'))) :
    N ≤ N' :=
  le_of_forall_ofHom_pullback_le q
    (mem_fpqcPrecoverage_of_mem_coveringPrecoverage _ (Or.inr (Or.inr (Or.inl rfl))) hq)
    N N' hN hN' h

/-- **The inclusion of quasi-coherent submodules descends along a single surjective flat
quasi-compact morphism** `q : T ⟶ X`. -/
theorem le_of_ofHom_pullback_le {T : Scheme.{u}} (q : T ⟶ X) [Surjective q] [QuasiCompact q]
    [Flat q] [F.IsQuasicoherent] (N N' : F.Submodule)
    (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hN' : (N'.toSheafOfModules : X.Modules).IsQuasicoherent)
    (h : ofHom ((Scheme.Modules.pullback q).map (inclusion N)) ≤
      ofHom ((Scheme.Modules.pullback q).map (inclusion N'))) :
    N ≤ N' :=
  le_of_forall_ofHom_pullback_le (fun _ : Unit => q) (ofArrows_unit_mem_fpqcPrecoverage q)
    N N' hN hN' fun _ => h

end Descent

end Stacks.FiniteTypeSubmodule

end
