module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Morphisms of coherent adic systems are morphisms of their limits

Let `X` be a locally Noetherian scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. A coherent
adic system `(𝒢_n)` in `Coh(X, ℐ)` is in particular an adic inverse system of quasi-coherent
modules, so the reduction theorem for those systems identifies `𝒢_n` with
`(lim 𝒢_m) / ℐ ⁿ⁺¹ (lim 𝒢_m)`, compatibly with the limit projection. Two consequences are
recorded here. Each limit projection `lim 𝒢_m ⟶ 𝒢_n` is an epimorphism, being a cokernel
projection; and a morphism `a : lim 𝒢_m ⟶ lim ℋ_m` of the limit sheaves descends to the
quotients, producing a morphism `(𝒢_n) ⟶ (ℋ_n)` in `Coh(X, ℐ)` whose limit is `a` again. Taking
limits is therefore faithful on `Coh(X, ℐ)`.

The last section turns this into the uniqueness statement the construction of the comparison map
of [Stacks, Tag 088B] needs: if `c : ℋ ⟶ D` is a morphism of inverse systems which becomes an
isomorphism on limits, then composition with `c` sends morphisms `𝒢 ⟶ ℋ` of coherent adic
systems onto morphisms `𝒢 ⟶ D` of inverse systems, injectively.

## Main definitions

* `Stacks.Coherent.limitMapComponent` — the component at `n` of the morphism induced by a
  morphism of the limits.
* `Stacks.Coherent.coherentAdicSystemMapOfLimitMap` — **the morphism of coherent adic systems
  induced by a morphism of their limits.**
* `Stacks.Coherent.systemMapOfComparisonIso` — the morphism `𝒢 ⟶ ℋ` factoring a morphism
  `γ : 𝒢 ⟶ D` through a comparison morphism `c : ℋ ⟶ D` that is an isomorphism on limits.

## Main results

* `Stacks.Coherent.coherentAdicSystem_exists_limitQuotientIso` — the term at `n` of a coherent
  adic system is the reduction of the limit modulo `ℐ ⁿ⁺¹`.
* `Stacks.Coherent.coherentAdicSystem_epi_limit_π` — the limit projections are epimorphisms.
* `Stacks.Coherent.coherentAdicSystemMapOfLimitMap_limMap` — the induced morphism has the given
  morphism as its limit.
* `Stacks.Coherent.coherentAdicSystem_limMap_injective` — **taking limits is faithful on
  `Coh(X, ℐ)`.**
* `Stacks.Coherent.systemMapOfComparisonIso_comp` and
  `Stacks.Coherent.systemMap_unique_of_comparisonIso` — existence and uniqueness of the
  factorisation through a comparison morphism that is an isomorphism on limits.

## Implementation notes

The reduction theorem is `Stacks.Algebraization.AdicInverseSystem.exists_idealPowerQuotientIso`,
stated for the structure `Stacks.Algebraization.AdicInverseSystem`; a coherent adic system is
repackaged into one by a private definition. Coherence gives quasi-coherence of each term by
`isQuasicoherent_of_isCoherent`, and local Noetherianness makes every ideal sheaf of finite type,
which is the remaining hypothesis of the theorem.

The descent of `a : lim 𝒢_m ⟶ lim ℋ_m` to the quotients is
`Stacks.Algebraization.idealPowerQuotientMap` for the same ideal and the same exponent on both
sides. Its compatibility with the quotient projections, together with the two isomorphisms
supplied by the reduction theorem, is what makes the resulting family natural, and epiness of the
limit projections is what reduces naturality — and every other identity below — to an identity
between morphisms out of the limit.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and a
submodule inclusion has source an object of the second presentation while a limit of a diagram of
shape `ℕᵒᵖ ⥤ X.Modules` is an object of the first. A composite of the two is accepted, but its
inner and outer composition then mention different presentations and no rewrite by
`CategoryTheory.Category.assoc` applies to it. The reduction isomorphism is therefore restated at
`X.Modules` before anything is rewritten, and epiness of the quotient projection is taken from
`Stacks.Algebraization.epi_cokernel_π_submodule_ι`, which is stated at that presentation.

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

/-- On a locally Noetherian scheme every quasi-coherent ideal sheaf is of finite type: its ideal
on an affine open is an ideal of a Noetherian ring. -/
private alias idealSheafData_isFiniteType := AlgebraicGeometry.isFiniteType_of_isLocallyNoetherian

/-- A coherent adic system, repackaged as an adic inverse system of quasi-coherent modules. -/
private def coherentAdicInverseSystem {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : CoherentAdicSystems I) :
    Stacks.Algebraization.AdicInverseSystem.{u} where
  X := X
  I := I
  system := G.obj
  isQuasicoherent n := by
    have _ : (G.obj.obj n).IsCoherent := G.property.1 n.unop
    exact isQuasicoherent_of_isCoherent (G.obj.obj n)
  quotientIso n := (G.property.2.2 n).choose
  quotientIso_hom_comp n := (G.property.2.2 n).choose_spec

/-- **The term at `n` of a coherent adic system is the reduction of the limit modulo `ℐ ⁿ⁺¹`.**
The isomorphism carries the quotient projection to the limit projection. -/
public lemma coherentAdicSystem_exists_limitQuotientIso
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    (G : CoherentAdicSystems I) (n : ℕ) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient I (n + 1) (limit G.obj) ≅ G.obj.obj (op n),
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1) (limit G.obj)).ι ≫ e.hom =
        limit.π G.obj (op n) :=
  Stacks.Algebraization.AdicInverseSystem.exists_idealPowerQuotientIso
    (coherentAdicInverseSystem G) (idealSheafData_isFiniteType I) n

/-- The reduction isomorphism of `coherentAdicSystem_exists_limitQuotientIso`, restated so that
every composition in sight happens in `X.Modules`. -/
private lemma exists_limitQuotientIso' {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : CoherentAdicSystems I) (n : ℕ) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient I (n + 1) (limit G.obj) ≅ G.obj.obj (op n),
      cokernel.π (C := X.Modules)
          (Stacks.Algebraization.idealPowerMultiple I (n + 1) (limit G.obj)).ι ≫ e.hom =
        limit.π G.obj (op n) :=
  coherentAdicSystem_exists_limitQuotientIso G n

/-- **The limit projections of a coherent adic system are epimorphisms**, being cokernel
projections under the identification of the term at `n` with a reduction of the limit. -/
public lemma coherentAdicSystem_epi_limit_π
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    (G : CoherentAdicSystems I) (n : ℕᵒᵖ) : Epi (limit.π G.obj n) := by
  obtain ⟨e, he⟩ := exists_limitQuotientIso' G n.unop
  have h1 : Epi (cokernel.π (C := X.Modules)
      (Stacks.Algebraization.idealPowerMultiple I (n.unop + 1) (limit G.obj)).ι) :=
    Stacks.Algebraization.epi_cokernel_π_submodule_ι _
  rw [← he]
  exact epi_comp' h1 inferInstance

/-- Two morphisms out of a term of a coherent adic system agree if they agree after composing with
the limit projection. -/
private lemma eq_of_limit_π_comp_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (G : CoherentAdicSystems I) {n : ℕᵒᵖ} {Y : X.Modules}
    {f g : G.obj.obj n ⟶ Y} (h : limit.π G.obj n ≫ f = limit.π G.obj n ≫ g) : f = g := by
  have := coherentAdicSystem_epi_limit_π G n
  exact (cancel_epi (limit.π G.obj n)).mp h

/-- **A morphism of the limits descends to the terms of two coherent adic systems.** Transport the
descent of `a` to the reductions modulo `ℐ ⁿ⁺¹` along the two reduction isomorphisms. -/
public lemma exists_limitMapComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {G H : CoherentAdicSystems I}
    (a : limit G.obj ⟶ limit H.obj) (n : ℕ) :
    ∃ b : G.obj.obj (op n) ⟶ H.obj.obj (op n),
      limit.π G.obj (op n) ≫ b = a ≫ limit.π H.obj (op n) := by
  obtain ⟨eG, hG⟩ := exists_limitQuotientIso' G n
  obtain ⟨eH, hH⟩ := exists_limitQuotientIso' H n
  refine ⟨eG.inv ≫ Stacks.Algebraization.idealPowerQuotientMap I I (n + 1) (n + 1) le_rfl a ≫
    eH.hom, ?_⟩
  rw [← hG, ← hH, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
    Stacks.Algebraization.idealPowerQuotientMap_π, Category.assoc]

/-- The component at `n` of the morphism of coherent adic systems induced by a morphism of their
limits. -/
public def limitMapComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {G H : CoherentAdicSystems I}
    (a : limit G.obj ⟶ limit H.obj) (n : ℕ) : G.obj.obj (op n) ⟶ H.obj.obj (op n) :=
  (exists_limitMapComponent a n).choose

/-- The components of the induced morphism are compatible with the limit projections. -/
public lemma limitMapComponent_π {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {G H : CoherentAdicSystems I}
    (a : limit G.obj ⟶ limit H.obj) (n : ℕ) :
    limit.π G.obj (op n) ≫ limitMapComponent a n = a ≫ limit.π H.obj (op n) :=
  (exists_limitMapComponent a n).choose_spec

/-- **The morphism of coherent adic systems induced by a morphism of their limits.** Each
component is the descent of `a` to the reduction modulo `ℐ ⁿ⁺¹` of the two limits. -/
public def coherentAdicSystemMapOfLimitMap
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} (a : limit G.obj ⟶ limit H.obj) : G ⟶ H :=
  ObjectProperty.homMk
    { app n := limitMapComponent a n.unop
      naturality i j f := by
        letI := coherentAdicSystem_epi_limit_π G i
        apply (cancel_epi (limit.π G.obj i)).mp
        rw [← Category.assoc, limit.w, limitMapComponent_π, ← Category.assoc,
          limitMapComponent_π, Category.assoc, limit.w] }

/-- The morphism of coherent adic systems induced by `a` has `a` as its limit. -/
public lemma coherentAdicSystemMapOfLimitMap_limMap
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} (a : limit G.obj ⟶ limit H.obj) :
    limMap (coherentAdicSystemMapOfLimitMap a).hom = a := by
  refine limit.hom_ext fun n => ?_
  rw [limMap_π]
  exact limitMapComponent_π a n.unop

/-- **Taking limits is faithful on coherent adic systems**: two morphisms with the same limit are
equal, because the limit projections of the source are epimorphisms. -/
public lemma coherentAdicSystem_limMap_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} {a b : G ⟶ H}
    (h : limMap a.hom = limMap b.hom) : a = b := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  apply eq_of_limit_π_comp_eq G
  rw [← limMap_π, ← limMap_π, h]

/-- **Factorisation through a comparison morphism that is an isomorphism on limits.** Given
`c : ℋ ⟶ D` with `lim c` invertible and `γ : 𝒢 ⟶ D`, this is the morphism `𝒢 ⟶ ℋ` of coherent
adic systems whose limit is `lim γ ≫ (lim c)⁻¹`. -/
public def systemMapOfComparisonIso
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} {D : ℕᵒᵖ ⥤ X.Modules}
    (c : H.obj ⟶ D) [IsIso (limMap c)] (γ : G.obj ⟶ D) : G ⟶ H :=
  coherentAdicSystemMapOfLimitMap (limMap γ ≫ inv (limMap c))

/-- The factorisation through a comparison morphism does factor the given morphism. -/
public lemma systemMapOfComparisonIso_comp
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} {D : ℕᵒᵖ ⥤ X.Modules}
    (c : H.obj ⟶ D) [IsIso (limMap c)] (γ : G.obj ⟶ D) :
    (systemMapOfComparisonIso c γ).hom ≫ c = γ := by
  have key : ∀ n : ℕᵒᵖ, limit.π G.obj n ≫ (systemMapOfComparisonIso c γ).hom.app n =
      (limMap γ ≫ inv (limMap c)) ≫ limit.π H.obj n :=
    fun n => limitMapComponent_π (limMap γ ≫ inv (limMap c)) n.unop
  apply NatTrans.ext
  funext n
  apply eq_of_limit_π_comp_eq G
  rw [NatTrans.comp_app, ← Category.assoc, key n]
  simp only [Category.assoc]
  rw [← limMap_π c n]
  simp only [IsIso.inv_hom_id_assoc]
  exact limMap_π γ n

/-- **A morphism of coherent adic systems is determined by its composite with a comparison
morphism that is an isomorphism on limits.** -/
public lemma systemMap_unique_of_comparisonIso
    {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData}
    {G H : CoherentAdicSystems I} {D : ℕᵒᵖ ⥤ X.Modules}
    (c : H.obj ⟶ D) [IsIso (limMap c)] {a b : G ⟶ H}
    (h : a.hom ≫ c = b.hom ≫ c) : a = b := by
  refine coherentAdicSystem_limMap_injective
    ((cancel_mono (limMap c)).mp (limit.hom_ext fun n => ?_))
  rw [Category.assoc, Category.assoc, limMap_π, ← Category.assoc, ← Category.assoc,
    limMap_π, limMap_π, Category.assoc, Category.assoc]
  exact congrArg (fun k : G.obj ⟶ D => limit.π G.obj n ≫ k.app n) h

end Stacks.Coherent

end
