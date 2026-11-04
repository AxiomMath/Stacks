module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Algebraize
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualGlobal

/-!
# Comparing two coherent adic systems whose kernel and cokernel are annihilated

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and
`α : (F_n) ⟶ (G_n)` a morphism of `Coh(X, ℐ)` whose levelwise kernels and cokernels are
annihilated by one power of `ℐ`, which is the hypothesis of Stacks 0888 (1). Such an `α` is an
isomorphism "up to `ℐ`-power torsion", and the question Stacks 0EIU asks is which properties of a
coherent adic system it transports. This file proves that membership in the essential image of the
completion functor of Stacks 0880 transports *both ways* across such an `α`, and derives the
corresponding two-sided transport of extendability in the sense of
`Stacks.Algebraization.ExtendsToX`. Those are the two parts of Stacks 0EIU.

The two implications come from the two parts of Stacks 0889 and are not symmetric.

* From the *target* to the *source*: an isomorphism `(G_n) ≅ H^∧` presents `α` as a morphism *into*
  a completion, and `Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian` — Stacks
  0889 part (1) — produces a coherent module whose completion is `(F_n)`.
* From the *source* to the *target*: an isomorphism `(F_n) ≅ H^∧` presents `α` as a morphism *out
  of* a completion, and `Stacks.Algebraization.essImage_of_map_from_completion` — the
  essential-image consequence of Stacks 0889 part (2), glued from the affine case over the affine
  opens of `X` — produces a coherent module whose completion is `(G_n)`.

## Main results

* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_comp_iso` — the hypothesis of Stacks
  0888 (1) is unchanged by composing with an isomorphism of systems on the right.
* `Stacks.Algebraization.essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower` — if the
  target of such an `α` is the completion of a coherent module, so is its source.
* `Stacks.Algebraization.isCompletion_of_isCompletion_of_isKernelCokernelAnnihilatedByPower` —
  the same statement in Situation 0EHC, which is one implication of Stacks 0EIU part (2).
* `Stacks.Algebraization.extendsToX_of_extendsToX_of_isKernelCokernelAnnihilatedByPower` — if the
  target of such an `α` extends to `X`, so does its source; one implication of Stacks 0EIU
  part (1).
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iso_comp` — the hypothesis of Stacks
  0888 (1) is unchanged by composing with an isomorphism of systems on the *left*.
* `Stacks.Algebraization.essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower` — **the
  source of such an `α` is the completion of a coherent module if and only if its target is.**
* `Stacks.Algebraization.isCompletion_iff_isCompletion_of_isKernelCokernelAnnihilatedByPower` —
  **Stacks 0EIU part (2)**, the same statement in Situation 0EHC.
* `Stacks.Algebraization.extendsToX_iff_extendsToX_of_isKernelCokernelAnnihilatedByPower` —
  **Stacks 0EIU part (1)**: the source of such an `α` extends to `X` if and only if its target
  does.

## Implementation notes

Both parts of Stacks 0EIU are "if and only if" statements, and the implication that needs Stacks
0889 part (2) — algebraization of a morphism *out of* a completion — is the one from the source of
`α` to its target. Only the essential-image consequence of part (2) is used:
`Stacks.Algebraization.essImage_of_map_from_completion` produces the coherent module and an
isomorphism of its completion with the given system, on a locally Noetherian scheme. Part (2) in
full, with the morphism `G ⟶ F` and the uniqueness clause, is
`Stacks.Algebraization.exists_unique_algebraization_dual_of_isNoetherian`.

The globalization of part (2) does not follow the shape of part (1): its mediating object would be
a pushout rather than the fibre product `Stacks.Algebraization.formalPullbackModule` that
globalizes part (1) with no gluing, so the affine theorem is glued over the affine opens instead.
See the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeAffineDual.lean` and of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeDualOverlap.lean`.

The route through `Ext` is not an alternative: the source derives the surjectivity of the `Ext`
comparison of Stacks 0EHP *from* part (2) of Stacks 0889, so using it here would be circular.

Composing with an isomorphism on the *left* changes neither the levelwise kernel nor the levelwise
cokernel either: the kernel because the isomorphism is invertible
(`CategoryTheory.Limits.kernelIsIsoComp`), and the cokernel because it is in particular an
epimorphism (`CategoryTheory.Limits.cokernelEpiComp`).

The transport of `Stacks.Algebraization.ExtendsToX` goes through Stacks 0EIN
(`Stacks.Algebraization.extendsToX_iff_pullback_isCompletion`), which replaces extendability over
the base by membership in the essential image over the adic completion of the base, and through
the flat-pullback transport of the hypothesis of Stacks 0888 (1),
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map`. The flatness of the
completion map is `Stacks.Algebraization.completionMap_flat` recomputed from
`AdicCompletion.flat_of_isNoetherian`, in the form in which the restriction to the open `U`
inherits it.

Composing with an isomorphism on the right changes neither the levelwise kernel nor the levelwise
cokernel: the kernel because the isomorphism is in particular a monomorphism
(`CategoryTheory.Limits.kernelCompMono`), and the cokernel because it is invertible
(`CategoryTheory.Limits.cokernelCompIsIso`). Annihilation by a fixed power of the ideal sheaf is
then carried across by `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso`.

## References

* [Stacks Project, Tag 0EIU](https://stacks.math.columbia.edu/tag/0EIU)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0EIN](https://stacks.math.columbia.edu/tag/0EIN)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Composing the comparison with an isomorphism -/

/-- Annihilation of levelwise kernels and cokernels by a power transports along isomorphisms of
the levelwise kernels and cokernels. -/
private theorem isKernelCokernelAnnihilatedByPower_of_iso {Y : Scheme.{u}}
    (J : Y.IdealSheafData) {F G F' G' : ℕᵒᵖ ⥤ Y.Modules} {α : F ⟶ G} {β : F' ⟶ G'}
    (hα : IsKernelCokernelAnnihilatedByPower J α)
    (hk : ∀ k : ℕ, kernel (β.app (op k)) ≅ kernel (α.app (op k)))
    (hc : ∀ k : ℕ, cokernel (β.app (op k)) ≅ cokernel (α.app (op k))) :
    IsKernelCokernelAnnihilatedByPower J β := by
  obtain ⟨t, ht, h⟩ := hα
  exact ⟨t, ht, fun k =>
    ⟨idealPowerMultiple_eq_bot_of_iso J (hk k) t (h k).1,
      idealPowerMultiple_eq_bot_of_iso J (hc k) t (h k).2⟩⟩

/-- **The hypothesis of Stacks 0888 (1) is stable under composing with an isomorphism.** If the
levelwise kernels and cokernels of `α` are annihilated by a power of `𝒥`, then so are those of
`α ≫ e` for an isomorphism `e` of the target.

The levelwise kernel is unchanged because `e` is a monomorphism, and the levelwise cokernel
because `e` is invertible; annihilation by a fixed power transports along those two
identifications. -/
public theorem isKernelCokernelAnnihilatedByPower_comp_iso {Y : Scheme.{u}}
    (J : Y.IdealSheafData) {F G H : ℕᵒᵖ ⥤ Y.Modules} (α : F ⟶ G) (e : G ≅ H)
    (hα : IsKernelCokernelAnnihilatedByPower J α) :
    IsKernelCokernelAnnihilatedByPower J (α ≫ e.hom) := by
  exact isKernelCokernelAnnihilatedByPower_of_iso J hα
    (fun k => kernelCompMono (α.app (op k)) (e.hom.app (op k)))
    (fun k => cokernelCompIsIso (α.app (op k)) (e.hom.app (op k)))

/-! ### Transporting membership in the essential image -/

/-- **One implication of the essential-image clause of Stacks 0EIU, on an arbitrary Noetherian
scheme.** Let `α : (F_n) ⟶ (G_n)` be a morphism of `Coh(Y, 𝒥)` whose levelwise kernels and
cokernels are annihilated by a power of `𝒥`. If `(G_n)` is the completion of a coherent
`𝒪_Y`-module, then so is `(F_n)`.

An isomorphism `(G_n) ≅ H^∧` turns `α` into a morphism `(F_n) ⟶ H^∧` into a completion, whose
levelwise kernels and cokernels are still annihilated by a power of `𝒥` by
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_comp_iso`. Stacks 0889 part (1), in the
form `Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian`, then produces a
coherent module `F` and an isomorphism `(F_n) ≅ F^∧`.

The converse implication comes from Stacks 0889 part (2); both together are
`Stacks.Algebraization.essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower`. -/
public theorem essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower (Y : Scheme.{u})
    [IsNoetherian Y] (J : Y.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems J} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower J α.hom)
    (hG : (completionFunctor Y J).essImage G) :
    (completionFunctor Y J).essImage F := by
  obtain ⟨H, ⟨e⟩⟩ := hG
  let ei : ((completionFunctor Y J).obj H).obj ≅ G.obj :=
    (ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem J)).mapIso e
  obtain ⟨F', a, β, -⟩ :=
    exists_unique_algebraization_of_isNoetherian J H F (α.hom ≫ ei.symm.hom)
      (isKernelCokernelAnnihilatedByPower_comp_iso J α.hom ei.symm hα)
  exact ⟨F', ⟨(ObjectProperty.isoMk _ β).symm⟩⟩

/-! ### The two clauses of Stacks 0EIU in Situation 0EHC -/

/-- **One implication of Stacks 0EIU part (2).** In Situation 0EHC, let
`α : (F_n) ⟶ (F'_n)` be a morphism of `Coh(U, I𝒪_U)` whose levelwise kernels and cokernels are
annihilated by a power of `I𝒪_U`. If `(F'_n)` is the completion of a coherent `𝒪_U`-module, then
so is `(F_n)`.

This is
`Stacks.Algebraization.essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower` on the open
subscheme `U`, which is Noetherian because `X` is. The converse implication needs Stacks 0889
part (2). -/
public theorem isCompletion_of_isCompletion_of_isKernelCokernelAnnihilatedByPower
    (S : AlgebraizationSituation.{u})
    {F G : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower (S.Yι.ker.comap S.U.ι) α.hom)
    (hG : (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage G) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage F :=
  essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower S.U.toScheme _ α hα hG

/-- The completion map of an algebraization situation is flat. -/
private theorem flat_completionMap (S : AlgebraizationSituation.{u}) :
    Flat (completionMap S) :=
  Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian S.I))

/-- **One implication of Stacks 0EIU part (1).** In Situation 0EHC, let
`α : (F_n) ⟶ (F'_n)` be a morphism of `Coh(U, I𝒪_U)` whose levelwise kernels and cokernels are
annihilated by a power of `I𝒪_U`. If `(F'_n)` extends to `X`, then so does `(F_n)`.

Stacks 0EIN, in the form `Stacks.Algebraization.extendsToX_iff_pullback_isCompletion`, replaces
extendability to `X` by membership in the essential image of the completion functor on the
preimage `U'` of `U` in the spectrum of the `I`-adic completion of the base. The pullback along
that flat morphism carries `α` to a morphism of `Coh(U', I𝒪_{U'})` whose levelwise kernels and
cokernels are still annihilated by a power of the ideal, by
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map`, so
`Stacks.Algebraization.essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower` applies on
`U'`. The converse implication needs Stacks 0889 part (2). -/
public theorem extendsToX_of_extendsToX_of_isKernelCokernelAnnihilatedByPower
    (S : AlgebraizationSituation.{u})
    {F G : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower (S.Yι.ker.comap S.U.ι) α.hom)
    (hG : ExtendsToX S G) : ExtendsToX S F := by
  have hflat := flat_completionMap S
  have hflat' : Flat (completionMap S ∣_ S.U) := inferInstance
  exact (extendsToX_iff_pullback_isCompletion S F).2
    (essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower
      (completionMap S ⁻¹ᵁ S.U).toScheme _
      ((Stacks.Coherent.coherentAdicPullback (completionMap S ∣_ S.U)
        (S.Yι.ker.comap S.U.ι)).map α)
      (Stacks.Coherent.isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map
        (completionMap S ∣_ S.U) (S.Yι.ker.comap S.U.ι) α hα)
      ((extendsToX_iff_pullback_isCompletion S G).1 hG))

/-! ### Transporting membership in the essential image the other way -/

/-- **The hypothesis of Stacks 0888 (1) is stable under composing with an isomorphism on the
left.** If the levelwise kernels and cokernels of `α` are annihilated by a power of `𝒥`, then so
are those of `e.hom ≫ α` for an isomorphism `e` of the source.

The levelwise kernel is unchanged because `e` is invertible, and the levelwise cokernel because it
is in particular an epimorphism; annihilation by a fixed power transports along those two
identifications. This is the mirror of
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_comp_iso`, and it is what lets an
isomorphism of the *source* with a completion be absorbed into `α`. -/
public theorem isKernelCokernelAnnihilatedByPower_iso_comp {Y : Scheme.{u}}
    (J : Y.IdealSheafData) {F G H : ℕᵒᵖ ⥤ Y.Modules} (e : F ≅ G) (α : G ⟶ H)
    (hα : IsKernelCokernelAnnihilatedByPower J α) :
    IsKernelCokernelAnnihilatedByPower J (e.hom ≫ α) := by
  exact isKernelCokernelAnnihilatedByPower_of_iso J hα
    (fun k => kernelIsIsoComp (e.hom.app (op k)) (α.app (op k)))
    (fun k => cokernelEpiComp (e.hom.app (op k)) (α.app (op k)))

/-- **The essential-image clause of Stacks 0EIU on an arbitrary Noetherian scheme.** Let
`α : (F_n) ⟶ (G_n)` be a morphism of `Coh(Y, 𝒥)` whose levelwise kernels and cokernels are
annihilated by a power of `𝒥`. Then `(F_n)` is the completion of a coherent `𝒪_Y`-module if and
only if `(G_n)` is.

The implication from the target to the source is
`Stacks.Algebraization.essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower`, which is
Stacks 0889 part (1). The implication from the source to the target reads `α` through an
isomorphism `(F_n) ≅ H^∧`, which presents it as a morphism *out of* a completion still satisfying
the hypothesis of Stacks 0888 (1) by
`Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iso_comp`, and applies the
essential-image consequence of Stacks 0889 part (2),
`Stacks.Algebraization.essImage_of_map_from_completion`. -/
public theorem essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower (Y : Scheme.{u})
    [IsNoetherian Y] (J : Y.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems J} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower J α.hom) :
    (completionFunctor Y J).essImage F ↔ (completionFunctor Y J).essImage G := by
  refine ⟨fun hF => ?_, essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower Y J α hα⟩
  obtain ⟨H, ⟨e⟩⟩ := hF
  have ei : ((completionFunctor Y J).obj H).obj ≅ F.obj :=
    (ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem J)).mapIso e
  exact essImage_of_map_from_completion J H G (ei.hom ≫ α.hom)
    (isKernelCokernelAnnihilatedByPower_iso_comp J ei α.hom hα)

/-! ### The two clauses of Stacks 0EIU -/

/-- **Stacks 0EIU part (2).** In Situation 0EHC, let `α : (F_n) ⟶ (F'_n)` be a morphism of
`Coh(U, I𝒪_U)` whose levelwise kernels and cokernels are annihilated by a power of `I𝒪_U`. Then
`(F_n)` is the completion of a coherent `𝒪_U`-module if and only if `(F'_n)` is.

This is `Stacks.Algebraization.essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower` on the
open subscheme `U`, which is Noetherian because `X` is. -/
@[stacks 0EIU "part (2): membership in the essential image of the completion functor"]
public theorem isCompletion_iff_isCompletion_of_isKernelCokernelAnnihilatedByPower
    (S : AlgebraizationSituation.{u})
    {F G : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower (S.Yι.ker.comap S.U.ι) α.hom) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage F ↔
      (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage G :=
  essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower S.U.toScheme _ α hα

/-- **Stacks 0EIU part (1).** In Situation 0EHC, let `α : (F_n) ⟶ (F'_n)` be a morphism of
`Coh(U, I𝒪_U)` whose levelwise kernels and cokernels are annihilated by a power of `I𝒪_U`. Then
`(F_n)` extends to `X` if and only if `(F'_n)` does.

Stacks 0EIN, in the form `Stacks.Algebraization.extendsToX_iff_pullback_isCompletion`, replaces
extendability to `X` by membership in the essential image of the completion functor on the
preimage `U'` of `U` in the spectrum of the `I`-adic completion of the base. The pullback along
that flat morphism carries `α` to a morphism of `Coh(U', I𝒪_{U'})` whose levelwise kernels and
cokernels are still annihilated by a power of the ideal, by
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map`, so
`Stacks.Algebraization.essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower` applies on
`U'`. The flatness of the completion map is
`AdicCompletion.flat_of_isNoetherian` read through `AlgebraicGeometry.Flat.SpecMap_iff`, in the
form in which the restriction to the open `U` inherits it. -/
@[stacks 0EIU "part (1): extendability to the whole of X"]
public theorem extendsToX_iff_extendsToX_of_isKernelCokernelAnnihilatedByPower
    (S : AlgebraizationSituation.{u})
    {F G : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower (S.Yι.ker.comap S.U.ι) α.hom) :
    ExtendsToX S F ↔ ExtendsToX S G := by
  have hflat := flat_completionMap S
  have hflat' : Flat (completionMap S ∣_ S.U) := inferInstance
  have hα' := Stacks.Coherent.isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map
    (completionMap S ∣_ S.U) (S.Yι.ker.comap S.U.ι) α hα
  exact (extendsToX_iff_pullback_isCompletion S F).trans
    ((essImage_iff_essImage_of_isKernelCokernelAnnihilatedByPower
        (completionMap S ⁻¹ᵁ S.U).toScheme _
        ((Stacks.Coherent.coherentAdicPullback (completionMap S ∣_ S.U)
          (S.Yι.ker.comap S.U.ι)).map α) hα').trans
      (extendsToX_iff_pullback_isCompletion S G).symm)

end Stacks.Algebraization

end
