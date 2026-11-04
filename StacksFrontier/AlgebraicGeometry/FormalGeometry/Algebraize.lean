module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction

/-!
# Algebraizing a map into a completion on a locally Noetherian scheme

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. This file globalizes the affine
algebraization theorem: a morphism `α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are
annihilated by one power of `ℐ` is the completion of a morphism `a : F ⟶ G` out of a coherent
`𝒪_X`-module, through an isomorphism `β : (F_n) ≅ F^∧`.

No gluing is performed. The candidate `F` is the formal pullback
`G ×_{lim G / ℐ ⁿ⁺¹ G} lim F_n` of `Stacks.Algebraization.formalPullbackModule`, a single global
object; the content of the globalization is that this object is coherent and that its completion
is `(F_n)`. Both are checked affine-locally, and the local input is the affine case
`Stacks.Algebraization.affine_exists_algebraization`, applied on each affine open `U` to the
restricted datum. Two steps make that application legitimate. The ideal sheaf `ℐ|_U` on an affine
open is the one attached to an ideal of `Γ(U, ⊤)`, by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, which is the form the affine theorem is
stated in. And the hypothesis on `α` restricts: restriction along an open immersion is exact, so
it carries the levelwise kernels and cokernels of `α` to those of the restricted morphism, and it
preserves annihilation by a power of the ideal sheaf.

The comparison map `F^∧ ⟶ (F_n)` is global and canonical: it is the adjunct, under
`Stacks.Algebraization.completionHomLimitEquiv`, of the second projection
`F ⟶ lim F_n` of the formal pullback. Reading `α` through it is the factorization `α = a^∧ ∘ β`,
checked levelwise against the epimorphisms `F ⟶ F / ℐ ⁿ⁺¹ F`. That it is invertible is local on
`X` by `Stacks.Coherent.isIso_of_isIso_restrictFunctor_map_system`, and over an affine open the
local algebraization identifies it: both the restricted comparison map and the local algebraization
are adjuncts of maps into `lim F_n|_U`, and those two maps agree because the formal pullback
commutes with restriction.

## Main definitions

* `Stacks.Algebraization.coherentFormalPullback` — the formal pullback of `(G, (F_n), α)`, as a
  coherent `𝒪_X`-module, together with its projection
  `Stacks.Algebraization.coherentFormalPullbackMap` to `G` and the canonical comparison map
  `Stacks.Algebraization.coherentFormalPullbackCompare` from its completion to `(F_n)`.

## Main results

* `Stacks.Algebraization.affine_exists_algebraization_of_idealSheafData` — the affine case of
  Stacks 0889 (1) for an arbitrary quasi-coherent ideal sheaf on an affine scheme.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_restrictedSystemMap` — the hypothesis
  of Stacks 0888 (1) restricts along an open immersion.
* `Stacks.Algebraization.exists_local_algebraization` — over each affine open the restricted datum
  admits an algebraization.
* `Stacks.Algebraization.formalPullbackModule_isCoherent_of_annihilated` — the formal pullback is
  a coherent `𝒪_X`-module.
* `Stacks.Algebraization.isIso_of_isAdjunct` — a map of coherent adic systems out of a completion
  whose adjunct factors through an isomorphism of the system is itself an isomorphism.
* `Stacks.Algebraization.isIso_restrictFunctor_map_of_local_algebraization` — the restriction of
  such a comparison map to an open subscheme carrying a local algebraization is an isomorphism.
* `Stacks.Algebraization.coherentFormalPullbackCompare_comp` — reading `α` through the comparison
  map is the completion of the projection to `G`.
* `Stacks.Algebraization.isIso_coherentFormalPullbackCompare` — the comparison map is an
  isomorphism.
* `Stacks.Algebraization.restrict_coherentFormalPullbackMap_eq` and
  `Stacks.Algebraization.isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap` —
  over an affine open the projection to `G` is the local comparison map up to an isomorphism of
  its source, so its kernel and cokernel are annihilated there by a power of `ℐ|_U`.
* `Stacks.Algebraization.exists_algebraization` — the coherent module `F`, the morphism
  `a : F ⟶ G` and the isomorphism `β : (F_n) ≅ F^∧` through which `α` is the completion of `a`.
* `Stacks.Algebraization.exists_unique_algebraization` — **Stacks 0889 (1)**: the same triple
  together with the annihilation of the kernel and the cokernel of `a` and the uniqueness of the
  triple up to a unique isomorphism, given the locality of annihilation by a power of `ℐ`.
* `Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian` — the same statement with
  no hypothesis beyond `IsNoetherian X`, which is the hypothesis of the source.

## Implementation notes

Stacks 0889 (1) appears in three forms. `Stacks.Algebraization.exists_algebraization` is
unconditional and asserts the existence of the triple `(F, a, β)` with the factorization
`α = a^∧ ∘ β`, but not that the kernel and the cokernel of `a` are annihilated by a power of `ℐ`.
`Stacks.Algebraization.exists_unique_algebraization` asserts the whole of the source statement,
annihilation and uniqueness included, from one extra hypothesis: that a sheaf of modules
annihilated by a power of `ℐ|_U` over every affine open `U` is annihilated by a power of `ℐ`.
`Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian` asserts it with no extra
hypothesis at all, replacing local Noetherianity by `IsNoetherian X`.

That extra hypothesis is a matter of quantifier order rather than of geometry. The affine theorem
produces one exponent per affine open, while `Stacks.Algebraization.IsPowerAnnihilated` asks for a
single exponent valid on every affine open at once. Two facts bridge the gap, and both are
available for an arbitrary sheaf of modules: annihilation by a *fixed* power of `ℐ` may be checked
on an open covering, by `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict`, and the
exponent is made uniform by passing to a finite affine covering, which needs the quasi-compactness
of `X`. That is `Stacks.Algebraization.isPowerAnnihilated_of_restrict`, and it is why the source
states the result for a Noetherian rather than a locally Noetherian scheme. Since neither fact
needs quasi-coherence of the sheaf, nothing has to be known about the kernel and the cokernel of
`a` beyond their being objects of `X.Modules`. The weaker-hypothesis form is kept because it
asks only for `IsLocallyNoetherian X`, under which the uniform exponent genuinely may fail to
exist.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so a single object can occur in a goal under
two defeq but not syntactically equal spellings. Every limit and `limMap` below therefore names
its category explicitly as `(C := X.Modules)`, and the associativity rearrangements are chains of
`Category.assoc` and `congrArg` composed with `Eq.trans` rather than `calc` blocks or `rw` calls:
a `calc` step whose two sides are typed at the other presentation finds no transitivity instance,
and a rewrite motive mixing the two is not type correct at the transparency `rw` builds it at. For
the same reason the two isomorphisms that have to be unfolded — the comparison of a restricted
completion with the completion of a restriction, and the identification of a local algebraization
with the restricted formal pullback — are introduced by `let` rather than `have`, since the proofs
reduce their underlying morphisms.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### The affine case for an arbitrary ideal sheaf -/

/-- **The affine case of Stacks 0889 (1).** On an affine Noetherian scheme every quasi-coherent
ideal sheaf is the one attached to an ideal of the global sections, by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, so the affine algebraization theorem
holds for an arbitrary quasi-coherent ideal sheaf. -/
public theorem affine_exists_algebraization_of_idealSheafData (Y : Scheme.{u}) [IsAffine Y]
    [IsLocallyNoetherian Y] [IsNoetherianRing Γ(Y, ⊤)] (K : Y.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems K)
    (α : Fsys.obj ⟶ ((completionFunctor Y K).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower K α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (a : F ⟶ G)
      (β : Fsys.obj ≅ ((completionFunctor Y K).obj F).obj),
      α = β.hom ≫ ((completionFunctor Y K).map a).hom ∧
        IsPowerAnnihilated K (kernel (C := Y.Modules) a.hom) ∧
          IsPowerAnnihilated K (cokernel (C := Y.Modules) a.hom) := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal Γ(Y, ⊤), K = Scheme.IdealSheafData.ofIdealTop J :=
    ⟨_, (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply K).symm⟩
  subst hJ
  exact affine_exists_algebraization Y J G Fsys α hα

/-! ### Restricting the datum to an open subscheme -/

/-- **The hypothesis of Stacks 0888 (1) restricts.** If the levelwise kernels and cokernels of
`α` are annihilated by a power of `ℐ`, then so are those of the datum transported to an open
subscheme.

Restriction along an open immersion is exact, so it carries the levelwise kernel and cokernel of
`α` to those of the restricted morphism — up to composing with the comparison isomorphism of
Stacks 0880, which changes neither — and it preserves annihilation by a power of the ideal
sheaf. -/
public theorem isKernelCokernelAnnihilatedByPower_restrictedSystemMap {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    IsKernelCokernelAnnihilatedByPower (I.comap f) (restrictedSystemMap f I G Fsys α) := by
  obtain ⟨t, ht, h⟩ := hα
  refine ⟨t, ht, fun k => ⟨?_, ?_⟩⟩ <;>
    have hmono : IsIso ((completionRestrictOpenIso f I G).hom.app (op k)) :=
      NatIso.isIso_app_of_isIso _ _
  · have hiso : (Scheme.Modules.restrictFunctor f).obj
          (kernel (C := X.Modules) (α.app (op k))) ≅
        kernel (C := Y.Modules) ((restrictedSystemMap f I G Fsys α).app (op k)) :=
      PreservesKernel.iso (Scheme.Modules.restrictFunctor f) (α.app (op k)) ≪≫
        (kernelCompMono ((Scheme.Modules.restrictFunctor f).map (α.app (op k)))
          ((completionRestrictOpenIso f I G).hom.app (op k))).symm
    exact idealPowerMultiple_eq_bot_of_iso (I.comap f) hiso.symm t
      (idealPowerMultiple_restrict_eq_bot f I t _ (h k).1)
  · have hiso : (Scheme.Modules.restrictFunctor f).obj
          (cokernel (C := X.Modules) (α.app (op k))) ≅
        cokernel (C := Y.Modules) ((restrictedSystemMap f I G Fsys α).app (op k)) :=
      PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) (α.app (op k)) ≪≫
        (cokernelCompIsIso ((Scheme.Modules.restrictFunctor f).map (α.app (op k)))
          ((completionRestrictOpenIso f I G).hom.app (op k))).symm
    exact idealPowerMultiple_eq_bot_of_iso (I.comap f) hiso.symm t
      (idealPowerMultiple_restrict_eq_bot f I t _ (h k).2)

/-- **Algebraization over an affine open.** The datum restricted to an affine open `U` admits an
algebraization along `ℐ|_U`, whose comparison map has kernel and cokernel annihilated by a power
of `ℐ|_U`.

This is the affine theorem applied on `U`: the restricted system is a coherent `ℐ|_U`-adic
system, the restricted morphism still satisfies the hypothesis of Stacks 0888 (1), and the ring
`Γ(U, ⊤)` is Noetherian because `X` is locally Noetherian. -/
public theorem exists_local_algebraization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) (U : X.affineOpens) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
      (b : F ⟶ restrictCoherentModules U.1.ι G)
      (β : ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj ≅
        ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj F).obj),
      restrictedSystemMap U.1.ι I G Fsys α =
          β.hom ≫ ((completionFunctor U.1.toScheme (I.comap U.1.ι)).map b).hom ∧
        IsPowerAnnihilated (I.comap U.1.ι)
            (kernel (C := U.1.toScheme.Modules) b.hom) ∧
          IsPowerAnnihilated (I.comap U.1.ι)
            (cokernel (C := U.1.toScheme.Modules) b.hom) := by
  have hAff : IsAffine U.1.toScheme := U.2
  have hNRX : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hNR : IsNoetherianRing Γ(U.1.toScheme, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U.1)).symm.commRingCatIsoToRingEquiv
  exact affine_exists_algebraization_of_idealSheafData U.1.toScheme (I.comap U.1.ι)
    (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
    (restrictedSystemMap U.1.ι I G Fsys α)
    (isKernelCokernelAnnihilatedByPower_restrictedSystemMap U.1.ι I G Fsys α hα)

/-! ### Coherence of the formal pullback -/

/-- **The formal pullback is coherent.** Coherence is local on the base, and over each affine open
the formal pullback of the restricted datum is the local algebraization, which is coherent.

The affine-local hypothesis of `Stacks.Algebraization.formalPullbackModule_isCoherent` is
discharged by `Stacks.Algebraization.exists_local_algebraization`, whose annihilation conclusions
are converted to the affine-sections form that the invertibility criterion consumes. -/
public theorem formalPullbackModule_isCoherent_of_annihilated {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    (formalPullbackModule X I G Fsys α).IsCoherent := by
  refine formalPullbackModule_isCoherent I G Fsys α fun U => ?_
  obtain ⟨F, b, β, hβ, hK, hC⟩ := exists_local_algebraization I G Fsys α hα U
  have hFq : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent F.obj
  have hGq : (restrictCoherentModules U.1.ι G).obj.IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  exact ⟨F, b, β, hβ,
    fun V => isIPowerTorsion_ker_affineSectionMap (I.comap U.1.ι) b.hom hK V,
    fun V => isIPowerTorsion_cokernel_affineSectionMap (I.comap U.1.ι) b.hom hC V⟩

/-! ### The canonical comparison map and its invertibility -/

/-- Reading `completionToLimit` through `limMap γ` and projecting is the completion projection
followed by `γ`. -/
private theorem completionToLimit_comp_limMap_comp_π {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {Fsys : ℕᵒᵖ ⥤ X.Modules} (γ : ((completionFunctor X I).obj G).obj ⟶ Fsys) (n : ℕᵒᵖ) :
    (completionToLimit X I G ≫ limMap (C := X.Modules) γ) ≫ limit.π Fsys n =
      completionProjection X I G n.unop ≫ γ.app n :=
  (Category.assoc (obj := X.Modules) _ _ _).trans
    ((congrArg (completionToLimit X I G ≫ ·) (limMap_π (C := X.Modules) γ n)).trans
      ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        (congrArg (· ≫ γ.app n) (completionToLimit_projection X I G n))))

/-- The naturality of the completion projections, read on the limit through `limMap γ`. -/
private theorem comp_completionToLimit_limMap_comp_π {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (d : F ⟶ F')
    {Fsys : ℕᵒᵖ ⥤ X.Modules} (γ : ((completionFunctor X I).obj F').obj ⟶ Fsys) (n : ℕᵒᵖ) :
    (d.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) γ)) ≫ limit.π Fsys n =
      completionProjection X I F n.unop ≫ (((completionFunctor X I).map d).hom.app n ≫ γ.app n) :=
  (Category.assoc (obj := X.Modules) _ _ _).trans
    ((congrArg (d.hom ≫ ·) (completionToLimit_comp_limMap_comp_π I F' γ n)).trans
      ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (· ≫ γ.app n) (completionFunctor_map_quotient X I d n.unop).symm).trans
          (Category.assoc (obj := X.Modules) _ _ _))))

/-- **A comparison map identified by its adjunct is invertible.** Let `ζ : H^∧ ⟶ (F_n)` be a map
of coherent adic systems whose adjunct `w : H ⟶ lim F_n` factors as an isomorphism `c : H ⟶ F'`
followed by the map `F' ⟶ lim F_n` attached to an isomorphism `βl : (F_n) ≅ F'^∧`. Then `ζ` is an
isomorphism.

Both `ζ` and the composite `c^∧` followed by `βl⁻¹` have adjunct `w`, and the adjunction
`Stacks.Algebraization.completionHomLimitEquiv` is injective because the projections
`H ⟶ H / ℐ ⁿ⁺¹ H` are epimorphisms; so `ζ` is that composite, which is invertible. -/
public theorem isIso_of_isAdjunct {Y : Scheme.{u}} [IsLocallyNoetherian Y] (K : Y.IdealSheafData)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (Fs : Stacks.Coherent.CoherentAdicSystems K)
    (ζ : (completionFunctor Y K).obj H ⟶ Fs)
    (w : H.obj ⟶ limit (C := Y.Modules) Fs.obj)
    (hζ : ∀ n : ℕᵒᵖ, completionProjection Y K H n.unop ≫ ζ.hom.app n =
      w ≫ limit.π (C := Y.Modules) Fs.obj n)
    (F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (c : H ⟶ F')
    (hc : IsIso c) (βl : Fs.obj ≅ ((completionFunctor Y K).obj F').obj)
    (hw : c.hom ≫ (completionToLimit Y K F' ≫ limMap (C := Y.Modules) βl.inv) = w) :
    IsIso ζ := by
  have hci : IsIso c := hc
  have heq : ζ = (completionFunctor Y K).map c ≫ (ObjectProperty.isoMk _ βl).inv := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    have hepi := epi_completionProjection Y K H n.unop
    refine (@cancel_epi _ _ _ _ _ (completionProjection Y K H n.unop) hepi _ _).mp ?_
    exact (hζ n).trans ((congrArg (· ≫ limit.π (C := Y.Modules) Fs.obj n) hw.symm).trans
      (comp_completionToLimit_limMap_comp_π K c βl.inv n))
  rw [heq]
  infer_instance

/-- **The restriction of a comparison map to an open carrying a local algebraization.** If
`ζ : P^∧ ⟶ (F_n)` has adjunct `v : P ⟶ lim F_n`, and over an open subscheme `Y` the restriction
of `v` factors through an isomorphism `c : P|_Y ⟶ F'` and an isomorphism
`βl : (F_n)|_Y ≅ F'^∧`, then the restriction of `ζ` to `Y` is an isomorphism.

Restricting `ζ` and composing with the comparison isomorphism of Stacks 0880 gives a map
`(P|_Y)^∧ ⟶ (F_n)|_Y` whose adjunct is the restriction of `v` read through the identification of
the restricted limit with the limit of the restricted system; the previous lemma applies to it. -/
public theorem isIso_restrictFunctor_map_of_local_algebraization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (ζ : (completionFunctor X I).obj P ⟶ Fsys)
    (v : P.obj ⟶ limit (C := X.Modules) Fsys.obj)
    (hζ : ∀ n : ℕᵒᵖ, completionProjection X I P n.unop ≫ ζ.hom.app n =
      v ≫ limit.π (C := X.Modules) Fsys.obj n)
    (F' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (c : restrictCoherentModules f P ⟶ F') (hc : IsIso c)
    (βl : ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj ≅
      ((completionFunctor Y (I.comap f)).obj F').obj)
    (hw : c.hom ≫ (completionToLimit Y (I.comap f) F' ≫ limMap (C := Y.Modules) βl.inv) =
      (Scheme.Modules.restrictFunctor f).map v ≫ (restrictSystemLimitIso f I Fsys).hom) :
    IsIso ((Stacks.Coherent.restrictFunctor I f).map ζ) := by
  have hpl : PreservesLimit Fsys.obj (Scheme.Modules.restrictFunctor f) :=
    (preservesLimitsOfShape_natOp_restrictFunctor f).preservesLimit
  let heiso : (completionFunctor Y (I.comap f)).obj (restrictCoherentModules f P) ≅
      (Stacks.Coherent.restrictFunctor I f).obj ((completionFunctor X I).obj P) :=
    ObjectProperty.isoMk _ (completionRestrictOpenIso f I P).symm
  have hδ : IsIso (heiso.hom ≫ (Stacks.Coherent.restrictFunctor I f).map ζ) := by
    refine isIso_of_isAdjunct (I.comap f) (restrictCoherentModules f P)
      ((Stacks.Coherent.restrictFunctor I f).obj Fsys) _
      ((Scheme.Modules.restrictFunctor f).map v ≫ (restrictSystemLimitIso f I Fsys).hom)
      (fun n => ?_) F' c hc βl hw
    have hid : (completionRestrictOpenIso f I P).hom.app n ≫
        (completionRestrictOpenIso f I P).inv.app n = 𝟙 _ :=
      congrArg
        (fun k : (((completionFunctor X I).obj P).obj ⋙ Scheme.Modules.restrictFunctor f) ⟶
            (((completionFunctor X I).obj P).obj ⋙ Scheme.Modules.restrictFunctor f) => k.app n)
        (completionRestrictOpenIso f I P).hom_inv_id
    have c1 : completionProjection Y (I.comap f) (restrictCoherentModules f P) n.unop ≫
          (completionRestrictOpenIso f I P).inv.app n =
        ((Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
            (completionRestrictOpenIso f I P).hom.app n) ≫
          (completionRestrictOpenIso f I P).inv.app n :=
      congrArg (fun z => z ≫ (completionRestrictOpenIso f I P).inv.app n)
        (completionProjection_comp_completionRestrictOpenIso f I P n.unop).symm
    have c2 : ((Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
            (completionRestrictOpenIso f I P).hom.app n) ≫
          (completionRestrictOpenIso f I P).inv.app n =
        (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
          ((completionRestrictOpenIso f I P).hom.app n ≫
            (completionRestrictOpenIso f I P).inv.app n) := Category.assoc _ _ _
    have c3 : (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
          ((completionRestrictOpenIso f I P).hom.app n ≫
            (completionRestrictOpenIso f I P).inv.app n) =
        (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫ 𝟙 _ :=
      congrArg (fun z => (Scheme.Modules.restrictFunctor f).map
        (completionProjection X I P n.unop) ≫ z) hid
    have hce : completionProjection Y (I.comap f) (restrictCoherentModules f P) n.unop ≫
          (completionRestrictOpenIso f I P).inv.app n =
        (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) :=
      c1.trans (c2.trans (c3.trans (Category.comp_id _)))
    have hππ : (restrictSystemLimitIso f I Fsys).hom ≫
          limit.π (C := Y.Modules)
            ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj n =
        (Scheme.Modules.restrictFunctor f).map (limit.π (C := X.Modules) Fsys.obj n) :=
      preservesLimitIso_hom_π _ _ _
    have d1 : completionProjection Y (I.comap f) (restrictCoherentModules f P) n.unop ≫
          ((completionRestrictOpenIso f I P).inv.app n ≫
            (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n)) =
        (completionProjection Y (I.comap f) (restrictCoherentModules f P) n.unop ≫
            (completionRestrictOpenIso f I P).inv.app n) ≫
          (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n) := (Category.assoc _ _ _).symm
    have d2 : (completionProjection Y (I.comap f) (restrictCoherentModules f P) n.unop ≫
            (completionRestrictOpenIso f I P).inv.app n) ≫
          (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n) =
        (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
          (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n) :=
      congrArg (fun z => z ≫ (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n)) hce
    have d3 : (Scheme.Modules.restrictFunctor f).map (completionProjection X I P n.unop) ≫
          (Scheme.Modules.restrictFunctor f).map (ζ.hom.app n) =
        (Scheme.Modules.restrictFunctor f).map
          (completionProjection X I P n.unop ≫ ζ.hom.app n) :=
      ((Scheme.Modules.restrictFunctor f).map_comp _ _).symm
    have d4 : (Scheme.Modules.restrictFunctor f).map
          (completionProjection X I P n.unop ≫ ζ.hom.app n) =
        (Scheme.Modules.restrictFunctor f).map (v ≫ limit.π (C := X.Modules) Fsys.obj n) :=
      congrArg (fun z => (Scheme.Modules.restrictFunctor f).map z) (hζ n)
    have d5 : (Scheme.Modules.restrictFunctor f).map
          (v ≫ limit.π (C := X.Modules) Fsys.obj n) =
        (Scheme.Modules.restrictFunctor f).map v ≫
          (Scheme.Modules.restrictFunctor f).map (limit.π (C := X.Modules) Fsys.obj n) :=
      (Scheme.Modules.restrictFunctor f).map_comp _ _
    have d6 : (Scheme.Modules.restrictFunctor f).map v ≫
          (Scheme.Modules.restrictFunctor f).map (limit.π (C := X.Modules) Fsys.obj n) =
        (Scheme.Modules.restrictFunctor f).map v ≫
          ((restrictSystemLimitIso f I Fsys).hom ≫ limit.π (C := Y.Modules)
            ((Stacks.Coherent.restrictFunctor I f).obj Fsys).obj n) :=
      congrArg (fun z => (Scheme.Modules.restrictFunctor f).map v ≫ z) hππ.symm
    exact d1.trans (d2.trans (d3.trans (d4.trans (d5.trans
      (d6.trans (Category.assoc _ _ _).symm)))))
  exact IsIso.of_isIso_comp_left heiso.hom _

/-- The formal pullback of the datum `(G, (F_n), α)`, as a coherent `𝒪_X`-module. -/
public noncomputable def coherentFormalPullback {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨formalPullbackModule X I G Fsys α,
    formalPullbackModule_isCoherent_of_annihilated I G Fsys α hα⟩

/-- The projection of the formal pullback to `G`, as a morphism of coherent modules. -/
public noncomputable def coherentFormalPullbackMap {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    coherentFormalPullback I G Fsys α hα ⟶ G :=
  ObjectProperty.homMk (formalPullbackFst X I G Fsys α)

/-- The canonical comparison map from the completion of the formal pullback to `(F_n)`. -/
public noncomputable def coherentFormalPullbackCompare {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    (completionFunctor X I).obj (coherentFormalPullback I G Fsys α hα) ⟶ Fsys :=
  homToAdicSystem (coherentFormalPullback I G Fsys α hα) Fsys (formalPullbackSnd X I G Fsys α)

/-- **The factorization of Stacks 0889 (1).** Reading `α` through the comparison map is the
completion of the projection of the formal pullback to `G`.

Both sides are tested against the epimorphism `P ⟶ P / ℐ ⁿ⁺¹ P`, where the statement becomes the
defining cartesian square of the formal pullback. -/
public theorem coherentFormalPullbackCompare_comp {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    (coherentFormalPullbackCompare I G Fsys α hα).hom ≫ α =
      ((completionFunctor X I).map (coherentFormalPullbackMap I G Fsys α hα)).hom := by
  refine NatTrans.ext (funext fun n => ?_)
  have hepi := epi_completionProjection X I (coherentFormalPullback I G Fsys α hα) n.unop
  refine (@cancel_epi _ _ _ _ _
    (completionProjection X I (coherentFormalPullback I G Fsys α hα) n.unop) hepi _ _).mp ?_
  have a1 : completionProjection X I (coherentFormalPullback I G Fsys α hα) n.unop ≫
        ((coherentFormalPullbackCompare I G Fsys α hα).hom.app n ≫ α.app n) =
      (completionProjection X I (coherentFormalPullback I G Fsys α hα) n.unop ≫
        (coherentFormalPullbackCompare I G Fsys α hα).hom.app n) ≫ α.app n :=
    (Category.assoc _ _ _).symm
  have a2 : (completionProjection X I (coherentFormalPullback I G Fsys α hα) n.unop ≫
          (coherentFormalPullbackCompare I G Fsys α hα).hom.app n) ≫ α.app n =
      (formalPullbackSnd X I G Fsys α ≫ limit.π (C := X.Modules) Fsys.obj n) ≫ α.app n :=
    congrArg (fun z => z ≫ α.app n)
      (completionProjection_homToAdicSystem (coherentFormalPullback I G Fsys α hα) Fsys
        (formalPullbackSnd X I G Fsys α) n)
  have a3 : (formalPullbackSnd X I G Fsys α ≫ limit.π (C := X.Modules) Fsys.obj n) ≫ α.app n =
      formalPullbackSnd X I G Fsys α ≫ (limit.π (C := X.Modules) Fsys.obj n ≫ α.app n) :=
    Category.assoc _ _ _
  have a4 : formalPullbackSnd X I G Fsys α ≫ (limit.π (C := X.Modules) Fsys.obj n ≫ α.app n) =
      formalPullbackSnd X I G Fsys α ≫ (limMap (C := X.Modules) α ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) :=
    congrArg (fun z => formalPullbackSnd X I G Fsys α ≫ z) (limMap_π α n).symm
  have a5 : formalPullbackSnd X I G Fsys α ≫ (limMap (C := X.Modules) α ≫
          limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) =
      (formalPullbackSnd X I G Fsys α ≫ limMap (C := X.Modules) α) ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n :=
    (Category.assoc _ _ _).symm
  have a6 : (formalPullbackSnd X I G Fsys α ≫ limMap (C := X.Modules) α) ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n =
      (formalPullbackFst X I G Fsys α ≫ completionToLimit X I G) ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n :=
    congrArg (fun z => z ≫ limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n)
      (formalPullback_condition X I G Fsys α).symm
  have a7 : (formalPullbackFst X I G Fsys α ≫ completionToLimit X I G) ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n =
      formalPullbackFst X I G Fsys α ≫ (completionToLimit X I G ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) :=
    Category.assoc _ _ _
  have a8 : formalPullbackFst X I G Fsys α ≫ (completionToLimit X I G ≫
        limit.π (C := X.Modules) ((completionFunctor X I).obj G).obj n) =
      formalPullbackFst X I G Fsys α ≫ completionProjection X I G n.unop :=
    congrArg (fun z => formalPullbackFst X I G Fsys α ≫ z)
      (completionToLimit_projection X I G n)
  exact (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans a8))))))).trans
    (completionFunctor_map_quotient X I (coherentFormalPullbackMap I G Fsys α hα) n.unop).symm

/-- Over an affine open the restricted formal pullback is identified with the local algebraization
by an isomorphism `c`, compatibly with the projections to `G` and to `lim F_n`. -/
private theorem exists_iso_local_algebraization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) (U : X.affineOpens) :
    ∃ (Floc : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
      (b : Floc ⟶ restrictCoherentModules U.1.ι G)
      (βloc : ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys).obj ≅
        ((completionFunctor U.1.toScheme (I.comap U.1.ι)).obj Floc).obj)
      (c : restrictCoherentModules U.1.ι (coherentFormalPullback I G Fsys α hα) ⟶ Floc)
      (p : Floc.obj ⟶ formalPullbackModule U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α)), IsIso c ∧
      IsPowerAnnihilated (I.comap U.1.ι) (kernel (C := U.1.toScheme.Modules) b.hom) ∧
      IsPowerAnnihilated (I.comap U.1.ι) (cokernel (C := U.1.toScheme.Modules) b.hom) ∧
      p ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α) = b.hom ∧
      c.hom ≫ p = (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom ∧
      c.hom ≫ (completionToLimit U.1.toScheme (I.comap U.1.ι) Floc ≫
          limMap (C := U.1.toScheme.Modules) βloc.inv) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (formalPullbackSnd X I G Fsys α) ≫
          (restrictSystemLimitIso U.1.ι I Fsys).hom := by
  obtain ⟨Floc, b, βloc, hβ, hbK, hbC⟩ := exists_local_algebraization I G Fsys α hα U
  have hAff : IsAffine U.1.toScheme := U.2
  have hFlocq : Floc.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent Floc.obj
  have hGq : (restrictCoherentModules U.1.ι G).obj.IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hp : IsIso (formalPullbackFromAlgebraization U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α) Floc b βloc hβ) :=
    formalPullbackFromAlgebraization_isIso U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G) ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α) Floc b βloc hβ
      (fun V => isIPowerTorsion_ker_affineSectionMap (I.comap U.1.ι) b.hom hbK V)
      (fun V => isIPowerTorsion_cokernel_affineSectionMap (I.comap U.1.ι) b.hom hbC V)
  let hciso : restrictCoherentModules U.1.ι (coherentFormalPullback I G Fsys α hα) ≅ Floc :=
    ObjectProperty.isoMk _ (formalPullbackRestrictionIso U.1.ι I G Fsys α ≪≫
      (@asIso _ _ _ _ _ hp).symm)
  have hcan : hciso.hom.hom ≫ (@asIso _ _ _ _ _ hp).hom =
      (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom ≫ z)
          (@asIso _ _ _ _ _ hp).symm.hom_inv_id).trans (Category.comp_id _))
  refine ⟨Floc, b, βloc, hciso.hom, (@asIso _ _ _ _ _ hp).hom, inferInstance, hbK, hbC,
    formalPullbackFromAlgebraization_fst U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G)
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α) Floc b βloc hβ, hcan, ?_⟩
  have b1 : hciso.hom.hom ≫
        (completionToLimit U.1.toScheme (I.comap U.1.ι) Floc ≫
          limMap (C := U.1.toScheme.Modules) βloc.inv) =
      hciso.hom.hom ≫
        ((@asIso _ _ _ _ _ hp).hom ≫
          formalPullbackSnd U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
            ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
            (restrictedSystemMap U.1.ι I G Fsys α)) :=
    congrArg (fun z => hciso.hom.hom ≫ z)
      (formalPullbackFromAlgebraization_snd U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α) Floc b βloc hβ).symm
  have b2 : hciso.hom.hom ≫
        ((@asIso _ _ _ _ _ hp).hom ≫
          formalPullbackSnd U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
            ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
            (restrictedSystemMap U.1.ι I G Fsys α)) =
      (hciso.hom.hom ≫ (@asIso _ _ _ _ _ hp).hom) ≫
        formalPullbackSnd U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
          ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
          (restrictedSystemMap U.1.ι I G Fsys α) := (Category.assoc _ _ _).symm
  have b3 : (hciso.hom.hom ≫ (@asIso _ _ _ _ _ hp).hom) ≫
        formalPullbackSnd U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
          ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
          (restrictedSystemMap U.1.ι I G Fsys α) =
      (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom ≫
        formalPullbackSnd U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
          ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
          (restrictedSystemMap U.1.ι I G Fsys α) :=
    congrArg (fun z => z ≫ formalPullbackSnd U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G)
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α)) hcan
  exact b1.trans (b2.trans (b3.trans
    (formalPullbackRestrictionIso_hom_snd U.1.ι I G Fsys α)))

/-- **The completion of the formal pullback is `(F_n)`.** The canonical comparison map is an
isomorphism.

Invertibility in `Coh(X, ℐ)` is local on `X`, and over an affine open the local algebraization
identifies the restricted comparison map: the formal pullback commutes with restriction, and the
canonical map of the local algebraization to the restricted formal pullback is an isomorphism, so
the restricted comparison map has the same adjunct as the local algebraization. -/
public theorem isIso_coherentFormalPullbackCompare {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    IsIso (coherentFormalPullbackCompare I G Fsys α hα) := by
  refine Stacks.Coherent.isIso_of_isIso_restrictFunctor_map_system I
    (coherentFormalPullbackCompare I G Fsys α hα) (fun U : X.affineOpens => U.1)
    (iSup_affineOpens_eq_top X) fun U => ?_
  obtain ⟨Floc, b, βloc, c, p, hc, -, -, -, -, hw⟩ :=
    exists_iso_local_algebraization I G Fsys α hα U
  exact isIso_restrictFunctor_map_of_local_algebraization U.1.ι I
    (coherentFormalPullback I G Fsys α hα) Fsys (coherentFormalPullbackCompare I G Fsys α hα)
    (formalPullbackSnd X I G Fsys α)
    (completionProjection_homToAdicSystem (coherentFormalPullback I G Fsys α hα) Fsys
      (formalPullbackSnd X I G Fsys α))
    Floc c hc βloc hw

/-! ### Annihilation of the kernel and cokernel of the projection, affine-locally -/

/-- **Over an affine open the projection of the formal pullback is the local comparison map.**
If `c` identifies `P|_U` with the source of the local comparison map `b` compatibly with the
canonical map of the local algebraization to the restricted formal pullback, then `c` followed by
`b` is the restriction of the projection `P ⟶ G`. -/
public theorem restrict_coherentFormalPullbackMap_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) (U : X.affineOpens)
    (Floc : AlgebraicGeometry.SheafOfModules.CoherentModules U.1.toScheme.ringCatSheaf)
    (b : Floc ⟶ restrictCoherentModules U.1.ι G)
    (p : Floc.obj ⟶ formalPullbackModule U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G)
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α))
    (hpb : p ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α) = b.hom)
    (c : restrictCoherentModules U.1.ι (coherentFormalPullback I G Fsys α hα) ⟶ Floc)
    (hc : c.hom ≫ p = (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom) :
    c.hom ≫ b.hom =
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (coherentFormalPullbackMap I G Fsys α hα).hom := by
  have c1 : c.hom ≫ b.hom =
      c.hom ≫ (p ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α)) :=
    congrArg (fun z => c.hom ≫ z) hpb.symm
  have c2 : c.hom ≫ (p ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α)) =
      (c.hom ≫ p) ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α) := (Category.assoc _ _ _).symm
  have c3 : (c.hom ≫ p) ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
        (restrictCoherentModules U.1.ι G)
        ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
        (restrictedSystemMap U.1.ι I G Fsys α) =
      (formalPullbackRestrictionIso U.1.ι I G Fsys α).hom ≫
        formalPullbackFst U.1.toScheme (I.comap U.1.ι) (restrictCoherentModules U.1.ι G)
          ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
          (restrictedSystemMap U.1.ι I G Fsys α) :=
    congrArg (fun z => z ≫ formalPullbackFst U.1.toScheme (I.comap U.1.ι)
      (restrictCoherentModules U.1.ι G)
      ((Stacks.Coherent.restrictFunctor I U.1.ι).obj Fsys)
      (restrictedSystemMap U.1.ι I G Fsys α)) hc
  exact c1.trans (c2.trans (c3.trans
    (formalPullbackRestrictionIso_hom_fst U.1.ι I G Fsys α)))

/-- **The kernel and the cokernel of the projection are annihilated by a power of `ℐ` over each
affine open.** Over `U` the projection is the local comparison map up to an isomorphism of its
source, so its kernel and cokernel restrict to those of the local comparison map, which the
affine theorem annihilates. -/
public theorem isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) (U : X.affineOpens) :
    IsPowerAnnihilated (I.comap U.1.ι)
        ((Scheme.Modules.restrictFunctor U.1.ι).obj
          (kernel (C := X.Modules) (coherentFormalPullbackMap I G Fsys α hα).hom)) ∧
      IsPowerAnnihilated (I.comap U.1.ι)
        ((Scheme.Modules.restrictFunctor U.1.ι).obj
          (cokernel (C := X.Modules) (coherentFormalPullbackMap I G Fsys α hα).hom)) := by
  obtain ⟨Floc, b, βloc, c, p, hc, hbK, hbC, hpb, hcp, -⟩ :=
    exists_iso_local_algebraization I G Fsys α hα U
  have hci : IsIso c.hom := inferInstance
  have hfst := restrict_coherentFormalPullbackMap_eq I G Fsys α hα U Floc b p hpb c hcp
  obtain ⟨nK, hnK⟩ := hbK
  obtain ⟨nC, hnC⟩ := hbC
  refine ⟨⟨nK, idealPowerMultiple_eq_bot_of_iso (I.comap U.1.ι) ?_ nK hnK⟩,
    ⟨nC, idealPowerMultiple_eq_bot_of_iso (I.comap U.1.ι) ?_ nC hnC⟩⟩
  · exact PreservesKernel.iso (Scheme.Modules.restrictFunctor U.1.ι)
      (coherentFormalPullbackMap I G Fsys α hα).hom ≪≫
      (kernelIsoOfEq hfst).symm ≪≫ kernelIsIsoComp c.hom b.hom
  · exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.1.ι)
      (coherentFormalPullbackMap I G Fsys α hα).hom ≪≫
      (cokernelIsoOfEq hfst).symm ≪≫ cokernelEpiComp c.hom b.hom

/-! ### The global algebraization -/

/-- The factorization `α = a^∧ ∘ β` through the inverse of the comparison map. -/
private theorem exists_iso_factorization_coherentFormalPullback {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ β : Fsys.obj ≅ ((completionFunctor X I).obj (coherentFormalPullback I G Fsys α hα)).obj,
      α = β.hom ≫ ((completionFunctor X I).map (coherentFormalPullbackMap I G Fsys α hα)).hom := by
  have hiso : IsIso (coherentFormalPullbackCompare I G Fsys α hα) :=
    isIso_coherentFormalPullbackCompare I G Fsys α hα
  have hid : (@asIso _ _ _ _ _ hiso).inv.hom ≫ (@asIso _ _ _ _ _ hiso).hom.hom = 𝟙 _ :=
    ObjectProperty.isoInv_hom_id_hom (@asIso _ _ _ _ _ hiso)
  exact ⟨(ObjectProperty.ι _).mapIso (@asIso _ _ _ _ _ hiso).symm,
    (Category.id_comp α).symm.trans
      ((congrArg (fun z => z ≫ α) hid.symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => (@asIso _ _ _ _ _ hiso).inv.hom ≫ z)
            (coherentFormalPullbackCompare_comp I G Fsys α hα))))⟩

/-- **Stacks 0889 (1), existence of the triple `(F, a, β)`.** Let `X` be a locally Noetherian
scheme, `ℐ` a quasi-coherent ideal sheaf, `G` a coherent `𝒪_X`-module and `(F_n)` a coherent
`ℐ`-adic system. A morphism `α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are
annihilated by a power of `ℐ` is the completion of a morphism `a : F ⟶ G` of coherent
`𝒪_X`-modules, read through an isomorphism `β : (F_n) ≅ F^∧`.

`F` is the formal pullback and `a` its projection to `G`; `β` is the inverse of the canonical
comparison map, which is an isomorphism by
`Stacks.Algebraization.isIso_coherentFormalPullbackCompare`, and the factorization is
`Stacks.Algebraization.coherentFormalPullbackCompare_comp` read through that inverse.

The clause of the source asserting that the kernel and the cokernel of `a` are annihilated by a
power of `ℐ` is not asserted here; it is available affine-locally as
`Stacks.Algebraization.isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap`,
and `Stacks.Algebraization.exists_unique_algebraization` records the full statement given the
passage from the affine-local form to the global one. -/
public theorem exists_algebraization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
      (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj),
      α = β.hom ≫ ((completionFunctor X I).map a).hom := by
  obtain ⟨β, hβ⟩ := exists_iso_factorization_coherentFormalPullback I G Fsys α hα
  exact ⟨_, coherentFormalPullbackMap I G Fsys α hα, β, hβ⟩

/-- **Stacks 0889 (1).** Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent ideal
sheaf, `G` a coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. A morphism
`α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are annihilated by a power of `ℐ`
admits a triple `(F, a, β)`, unique up to a unique isomorphism, with `F` a coherent
`𝒪_X`-module, `a : F ⟶ G` a morphism whose kernel and cokernel are annihilated by a power of
`ℐ`, `β : (F_n) ≅ F^∧` an isomorphism, and `α = a^∧ ∘ β`.

The triple is the formal pullback, its projection to `G` and the inverse of the canonical
comparison map, exactly as in `Stacks.Algebraization.exists_algebraization`; the annihilation of
the kernel and the cokernel of `a` is
`Stacks.Algebraization.isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap`
read through `hloc`, and the uniqueness clause is
`Stacks.Algebraization.unique_algebraization_of_isPowerAnnihilated`.

The hypothesis `hloc` says that a sheaf of modules annihilated by a power of `ℐ|_U` over every
affine open `U` is annihilated by a power of `ℐ`. It is two facts: annihilation by a *fixed* power
of `ℐ` is local on `X`, which is
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict`, and the exponent — of which the
affine theorem produces one per affine open — is made uniform by passing to a finite affine
covering, which needs the quasi-compactness of `X`. On a Noetherian scheme both are available and
`hloc` is discharged by `Stacks.Algebraization.isPowerAnnihilated_of_restrict`; that is
`Stacks.Algebraization.exists_unique_algebraization_of_isNoetherian`, and it is why the source
states the result for a Noetherian rather than a locally Noetherian scheme. The hypothesis is
retained here because quasi-compactness is exactly what `IsLocallyNoetherian X` does not
provide. -/
public theorem exists_unique_algebraization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (hloc : ∀ M : X.Modules,
      (∀ U : X.affineOpens, IsPowerAnnihilated (I.comap U.1.ι)
        ((Scheme.Modules.restrictFunctor U.1.ι).obj M)) → IsPowerAnnihilated I M)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
      (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj),
      (α = β.hom ≫ ((completionFunctor X I).map a).hom ∧
          IsPowerAnnihilated I (kernel (C := X.Modules) a.hom) ∧
            IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom)) ∧
        ∀ (F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a' : F' ⟶ G)
            (β' : Fsys.obj ≅ ((completionFunctor X I).obj F').obj),
          α = β'.hom ≫ ((completionFunctor X I).map a').hom →
            IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom) →
              IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom) →
                ∃! d : F.obj ≅ F'.obj,
                  d.hom ≫ a'.hom = a.hom ∧
                    d.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
                      completionToLimit X I F ≫ limMap (C := X.Modules) β.inv := by
  obtain ⟨β, hfac⟩ := exists_iso_factorization_coherentFormalPullback I G Fsys α hα
  have hK : IsPowerAnnihilated I
      (kernel (C := X.Modules) (coherentFormalPullbackMap I G Fsys α hα).hom) :=
    hloc _ fun U =>
      (isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap
        I G Fsys α hα U).1
  have hC : IsPowerAnnihilated I
      (cokernel (C := X.Modules) (coherentFormalPullbackMap I G Fsys α hα).hom) :=
    hloc _ fun U =>
      (isPowerAnnihilated_restrict_kernel_cokernel_coherentFormalPullbackMap
        I G Fsys α hα U).2
  refine ⟨coherentFormalPullback I G Fsys α hα, coherentFormalPullbackMap I G Fsys α hα,
    β, ⟨hfac, hK, hC⟩, fun F' a' β' hα' hKa' hCa' => ?_⟩
  exact unique_algebraization_of_isPowerAnnihilated I G Fsys α
    (coherentFormalPullback I G Fsys α hα) F' (coherentFormalPullbackMap I G Fsys α hα) a'
    β β' hfac hα' hK hC hKa' hCa'

/-- **Compatibility with the identifications of a formal system, read on the limit.** For coherent
`F`, `F'`, a morphism `d : F ⟶ F'` and isomorphisms `β : (F_n) ≅ F^∧` and `β' : (F_n) ≅ F'^∧`,
the square `β' = d^∧ ∘ β` commutes exactly when `d` intertwines the two maps
`F ⟶ lim F^∧ ⟶ lim (F_n)` and `F' ⟶ lim F'^∧ ⟶ lim (F_n)`.

One direction is the naturality of the projections `F ⟶ F/ℐ^{n+1}F` in `F`. For the other, a
morphism of inverse systems out of `F^∧` is determined by its composites with those projections,
which are epimorphisms. -/
public theorem completionMap_comp_eq_iff_limMap {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {F F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (d : F ⟶ F')
    {Fsys : ℕᵒᵖ ⥤ X.Modules}
    (β : Fsys ≅ ((completionFunctor X I).obj F).obj)
    (β' : Fsys ≅ ((completionFunctor X I).obj F').obj) :
    β.hom ≫ ((completionFunctor X I).map d).hom = β'.hom ↔
      d.hom ≫ (completionToLimit X I F' ≫ limMap (C := X.Modules) β'.inv) =
        completionToLimit X I F ≫ limMap (C := X.Modules) β.inv := by
  have hcomp : ∀ n : ℕᵒᵖ, (((completionFunctor X I).map d).hom ≫ β'.inv).app n =
      ((completionFunctor X I).map d).hom.app n ≫ β'.inv.app n := fun n =>
    NatTrans.comp_app _ _ n
  have hiff : β.hom ≫ ((completionFunctor X I).map d).hom = β'.hom ↔
      ((completionFunctor X I).map d).hom ≫ β'.inv = β.inv :=
    ((Iso.comp_inv_eq β').trans (Iso.eq_inv_comp β)).symm
  have h1 := comp_completionToLimit_limMap_comp_π I d β'.inv
  have h2 := completionToLimit_comp_limMap_comp_π I F β.inv
  refine hiff.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact limit.hom_ext (F := Fsys) fun n => (h1 n).trans
      ((congrArg (completionProjection X I F n.unop ≫ ·)
        ((hcomp n).symm.trans (congrArg (fun k => k.app n) h))).trans (h2 n).symm)
  · refine NatTrans.ext (funext fun n => ?_)
    exact (hcomp n).trans ((@cancel_epi X.Modules _ _ _ _ (completionProjection X I F n.unop)
      (epi_completionProjection X I F n.unop) _ _).1
      ((h1 n).symm.trans ((congrArg (· ≫ limit.π Fsys n) h).trans (h2 n))))

/-- **Stacks 0889 (1) on a Noetherian scheme.** Let `X` be a Noetherian scheme, `ℐ` a
quasi-coherent ideal sheaf, `G` a coherent `𝒪_X`-module and `(F_n)` a coherent `ℐ`-adic system. A
morphism `α : (F_n) ⟶ G^∧` whose levelwise kernels and cokernels are annihilated by a power of
`ℐ` admits a triple `(F, a, β)`, unique up to a unique isomorphism, with `F` a coherent
`𝒪_X`-module, `a : F ⟶ G` a morphism whose kernel and cokernel are annihilated by a power of
`ℐ`, `β : (F_n) ≅ F^∧` an isomorphism, and `α = a^∧ ∘ β`. Uniqueness: for a second such triple
`(F', a', β')` there is exactly one isomorphism `d : F ≅ F'` of triples, that is, with
`a' ∘ d = a` and `d^∧ ∘ β = β'`.

The existence is `Stacks.Algebraization.exists_unique_algebraization` with its one premise
supplied by `Stacks.Algebraization.isPowerAnnihilated_of_restrict`: on a Noetherian scheme the
affine-local annihilation of a sheaf of modules by powers of `ℐ|_U` is annihilation by a single
power of `ℐ`, because quasi-compactness extracts a finite affine covering and annihilation by a
fixed power is local on the base. The uniqueness there is read on `lim (F_n)`, and
`completionMap_comp_eq_iff_limMap` turns it into the compatibility `d^∧ ∘ β = β'`. The conditions
are exactly those of the source. -/
@[stacks 0889 "part (1): algebraization of a map into a completion"]
public theorem exists_unique_algebraization_of_isNoetherian {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : Fsys.obj ⟶ ((completionFunctor X I).obj G).obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    ∃ (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a : F ⟶ G)
      (β : Fsys.obj ≅ ((completionFunctor X I).obj F).obj),
      (α = β.hom ≫ ((completionFunctor X I).map a).hom ∧
          IsPowerAnnihilated I (kernel (C := X.Modules) a.hom) ∧
            IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom)) ∧
        ∀ (F' : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (a' : F' ⟶ G)
            (β' : Fsys.obj ≅ ((completionFunctor X I).obj F').obj),
          α = β'.hom ≫ ((completionFunctor X I).map a').hom →
            IsPowerAnnihilated I (kernel (C := X.Modules) a'.hom) →
              IsPowerAnnihilated I (cokernel (C := X.Modules) a'.hom) →
                ∃! d : F ≅ F',
                  d.hom ≫ a' = a ∧
                    β.hom ≫ ((completionFunctor X I).map d.hom).hom = β'.hom := by
  obtain ⟨F, a, β, hex, huniq⟩ :=
    exists_unique_algebraization I (fun M => isPowerAnnihilated_of_restrict I M) G Fsys α hα
  refine ⟨F, a, β, hex, fun F' a' β' hα' hK' hC' => ?_⟩
  obtain ⟨d₀, ⟨hd₀a, hd₀β⟩, hd₀u⟩ := huniq F' a' β' hα' hK' hC'
  refine ⟨ObjectProperty.isoMk _ d₀, ⟨ObjectProperty.hom_ext _ hd₀a,
    (completionMap_comp_eq_iff_limMap I (ObjectProperty.isoMk _ d₀).hom β β').2 hd₀β⟩,
    fun d hd => ?_⟩
  have hd₁ : (ObjectProperty.ι _).mapIso d = d₀ :=
    hd₀u _ ⟨congrArg (fun k => k.hom) hd.1,
      (completionMap_comp_eq_iff_limMap I d.hom β β').1 hd.2⟩
  exact Iso.ext (ObjectProperty.hom_ext _ (congrArg (fun e => e.hom) hd₁))

end Stacks.Algebraization

end
