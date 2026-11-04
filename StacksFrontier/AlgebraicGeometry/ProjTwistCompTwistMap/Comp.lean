module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Assembly
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Fibre
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Theta

/-!
# Tag 01MZ: the comparison maps on all twists of a composite compose

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings, let
`U(φ) ⊆ Proj ℬ` and `U(ψ) ⊆ Proj 𝒞` be their domains of definition, and let `V = r_ψ⁻¹(U(φ))`.
The third assertion of Stacks Tag 01MZ says that the comparison maps `θ` of Tag 01MY on the
twists compose: `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`, read on `U(ψ ∘ φ)` through the canonical
isomorphism `V ≅ U(ψ ∘ φ)` of the first assertion. This file proves it, for an arbitrary
composable pair and with **no hypothesis that any domain of definition is everything**.

The two sides are a three-factor and a nine-factor composite of components of the
pseudofunctoriality isomorphisms of the inverse image, and both are evaluated on a pulled-back
section by `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistComp_section`, at the level of
variables. What that statement asks for, and what is supplied here, is the identification of the
two sections of the `n`-th twist on `Proj 𝒞` that the two sides produce: the three-factor side
produces `θ_{ψ ∘ φ}` applied to the section, over the image under `U(ψ ∘ φ).ι` of
`r_{ψ∘φ}⁻¹(T)`, and the nine-factor side produces `θ_ψ` applied to `θ_φ` applied to it, over the
image under `U(ψ).ι` of `r_ψ⁻¹` of the image under `U(φ).ι` of `r_φ⁻¹(T)`. The two opens agree by
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.image_preimage_eq_of` and the two sections by
`twistSection_comp_val` below, whose content is the composition law for the comparison on fibres.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.mapDomainCompIso`: **the canonical isomorphism
  `V ≅ U(ψ ∘ φ)`** of Tag 01MZ's first assertion.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistComp_hom`: the two composites agree, at
  the level of variables, given what each of the three comparison maps does to a pulled-back
  section and the identification of the two sections of the target.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistSection_val_of`: **the comparison on
  sections at a point, with the prime of the source as a free argument.** The value is the fibre
  comparison applied to the value of the section at that prime.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistSection_comp_val`: **the comparison on
  sections of a composite, at a point.** The mathematical content of Tag 01MZ's third assertion:
  it is the composite of the two comparisons on sections, by
  `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.fibreMap_comp_apply`.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp_of`: Tag 01MZ's third assertion
  for **any** triple of morphisms of the shape the tag's first two assertions produce.
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`: **Stacks Tag 01MZ's third
  assertion** at the canonical isomorphism, with no hypothesis beyond composability.

## Implementation notes

Every prime is a free argument wherever one occurs, as in
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.fibreMap_comp_apply`: the two sides read the
section at the two primes `basePoint 𝒜 𝒞 (ψ ∘ φ) w` and `basePoint 𝒜 ℬ φ v` of `Proj 𝒜`, which
are equal because the homogeneous ideal of each is the preimage of one and the same homogeneous
ideal of `Proj 𝒞` — `HomogeneousIdeal.comap_comap` — but not definitionally so, and the fibre a
section takes its value in depends on the prime. `twistSection_val_of` is what keeps that
identification out of every type below: its prime is free and its two defining properties are
hypotheses.

Four further steps are taken at the level of variables, each because the same step at a domain of
definition exceeds the kernel's budget.

* Reading a point of an open as a point of the ambient projective spectrum is always taken from
  `Stacks.AlgebraicGeometry.ProjTwistCompare.liftPt_val` and
  `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.ambientPoint_val`, never by reduction.
* An equality of two sections of a twisting sheaf over two equal opens is reduced to an equality
  at every point by `twist_eq_map_eqToHom`, whose opens are variables; the reduction of the
  sections of the associated sheaf to a family of homogeneous fractions happens only there. The
  same statement written out at the two opens Tag 01MZ's two sides read over is a kernel timeout
  **in its statement**, before any proof is attempted.
* The identification of `(a ≫ b) ⁻¹ᵁ T` with `a ⁻¹ᵁ (b ⁻¹ᵁ T)`, which is definitional, is
  crossed only inside `hom_ext_of_pullbackSectionAt`, where the two morphisms are variables.
* **The three morphisms out of `V` are universally quantified in `twistMap_comp_of` and
  instantiated only in `twistMap_comp`, and the canonical isomorphism is a definition rather than
  a `let`.** Writing the assertion with those morphisms bound by `let`, as its shape invites,
  makes the kernel zeta-expand each of their thirteen occurrences inside the nine factors and
  exceed its deterministic budget; with them bound by `∀` the same proof checks in seconds, and
  the instance then costs one substitution.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w' w''

/-! ### Two generic reductions -/

section Hom

variable {X Y Z : Scheme.{u}}

/-- **Two morphisms out of the inverse image along a composite are equal as soon as they agree on
pulled-back sections**, read over the inverse image written as two successive inverse images.

This is `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.hom_ext_of_pullbackSectionOn` with
the identification of `(a ≫ b) ⁻¹ᵁ T` with `a ⁻¹ᵁ (b ⁻¹ᵁ T)` performed once, with the two
morphisms variables, where it is free. -/
public theorem hom_ext_of_pullbackSectionAt (a : X ⟶ Y) (b : Y ⟶ Z) {M : Z.Modules}
    {N : X.Modules} (α β : (Scheme.Modules.pullback (a ≫ b)).obj M ⟶ N)
    (h : ∀ (T : Z.Opens) (s : M.val.obj (op T)),
      α.val.app (op (a ⁻¹ᵁ (b ⁻¹ᵁ T)))
          (pullbackSectionAt (a ≫ b) M T (a ⁻¹ᵁ (b ⁻¹ᵁ T)) rfl s) =
        β.val.app (op (a ⁻¹ᵁ (b ⁻¹ᵁ T)))
          (pullbackSectionAt (a ≫ b) M T (a ⁻¹ᵁ (b ⁻¹ᵁ T)) rfl s)) :
    α = β := by
  refine hom_ext_of_pullbackSectionOn α β fun T s => ?_
  refine Eq.trans (congrArg (α.val.app (op ((a ≫ b) ⁻¹ᵁ T)))
    (pullbackSectionAt_comp_rfl a b M T rfl s).symm) ?_
  refine Eq.trans (h T s) ?_
  exact congrArg (β.val.app (op ((a ≫ b) ⁻¹ᵁ T))) (pullbackSectionAt_comp_rfl a b M T rfl s)

end Hom

section Nine

variable {W U UP UQ Pa Pb Pc : Scheme.{u}}
  (q : W ⟶ U) (dU : U ⟶ Pa) (iU : U ⟶ Pc)
  (p : W ⟶ UP) (dP : UP ⟶ Pa) (iP : UP ⟶ Pb)
  (jj : W ⟶ UQ) (dQ : UQ ⟶ Pb) (iQ : UQ ⟶ Pc)
  {Ma : Pa.Modules} {Mb : Pb.Modules} {Mc : Pc.Modules}

/-- **The three-factor and the nine-factor composite of Tag 01MZ's twist assertion agree**, at the
level of variables, given what each of the three comparison maps does to a pulled-back section
and the identification of the two sections of the target the two sides produce.

This is `twistComp_section` — the same statement on one pulled-back section — quantified over the
open and the section and then fed to `hom_ext_of_pullbackSectionAt`. Each comparison map is
described by an open `O` of its target, a section `s` over that open, and the identity saying that
the inverse image of `O` is the inverse image of the open one started from; those are the three
triples `OU, hOU, sU`, `OP, hOP, sP` and `OQ, hOQ, sQ`. -/
public theorem twistComp_hom
    (θ : (Scheme.Modules.pullback dU).obj Ma ⟶ (Scheme.Modules.pullback iU).obj Mc)
    (θP : (Scheme.Modules.pullback dP).obj Ma ⟶ (Scheme.Modules.pullback iP).obj Mb)
    (θQ : (Scheme.Modules.pullback dQ).obj Mb ⟶ (Scheme.Modules.pullback iQ).obj Mc)
    (hq : q ≫ dU = p ≫ dP) (hm : p ≫ iP = jj ≫ dQ) (ht : q ≫ iU = jj ≫ iQ)
    (OU : Pa.Opens → Pc.Opens) (hOU : ∀ T : Pa.Opens, iU ⁻¹ᵁ OU T = dU ⁻¹ᵁ T)
    (sU : ∀ T : Pa.Opens, Ma.val.obj (op T) → Mc.val.obj (op (OU T)))
    (hθ : ∀ (T : Pa.Opens) (s : Ma.val.obj (op T)),
      θ.val.app (op (dU ⁻¹ᵁ T)) (pullbackSectionOn dU Ma T s) =
        pullbackSectionAt iU Mc (OU T) (dU ⁻¹ᵁ T) (hOU T) (sU T s))
    (OP : Pa.Opens → Pb.Opens) (hOP : ∀ T : Pa.Opens, iP ⁻¹ᵁ OP T = dP ⁻¹ᵁ T)
    (sP : ∀ T : Pa.Opens, Ma.val.obj (op T) → Mb.val.obj (op (OP T)))
    (hθP : ∀ (T : Pa.Opens) (s : Ma.val.obj (op T)),
      θP.val.app (op (dP ⁻¹ᵁ T)) (pullbackSectionOn dP Ma T s) =
        pullbackSectionAt iP Mb (OP T) (dP ⁻¹ᵁ T) (hOP T) (sP T s))
    (OQ : Pb.Opens → Pc.Opens) (hOQ : ∀ T' : Pb.Opens, iQ ⁻¹ᵁ OQ T' = dQ ⁻¹ᵁ T')
    (sQ : ∀ T' : Pb.Opens, Mb.val.obj (op T') → Mc.val.obj (op (OQ T')))
    (hθQ : ∀ (T' : Pb.Opens) (t : Mb.val.obj (op T')),
      θQ.val.app (op (dQ ⁻¹ᵁ T')) (pullbackSectionOn dQ Mb T' t) =
        pullbackSectionAt iQ Mc (OQ T') (dQ ⁻¹ᵁ T') (hOQ T') (sQ T' t))
    (hT : ∀ T : Pa.Opens, OU T = OQ (OP T))
    (hsec : ∀ (T : Pa.Opens) (s : Ma.val.obj (op T)),
      Mc.val.map (eqToHom (congrArg op (hT T))) (sU T s) = sQ (OP T) (sP T s)) :
    (Scheme.Modules.pullbackComp q dU).inv.app Ma ≫
        (Scheme.Modules.pullback q).map θ ≫
        (Scheme.Modules.pullbackComp q iU).hom.app Mc =
      (Scheme.Modules.pullbackCongr hq).hom.app Ma ≫
        (Scheme.Modules.pullbackComp p dP).inv.app Ma ≫
        (Scheme.Modules.pullback p).map θP ≫
        (Scheme.Modules.pullbackComp p iP).hom.app Mb ≫
        (Scheme.Modules.pullbackCongr hm).hom.app Mb ≫
        (Scheme.Modules.pullbackComp jj dQ).inv.app Mb ≫
        (Scheme.Modules.pullback jj).map θQ ≫
        (Scheme.Modules.pullbackComp jj iQ).hom.app Mc ≫
        (Scheme.Modules.pullbackCongr ht).inv.app Mc := by
  refine hom_ext_of_pullbackSectionAt q dU _ _ fun T s => ?_
  exact twistComp_section q dU iU p dP iP jj dQ iQ θ θP θQ hq hm ht T s
    (OU T) (sU T s) (hOU T) (OP T) (sP T s) (hOP T)
    (OQ (OP T)) (sQ (OP T) (sP T s)) (hOQ (OP T))
    (hθ T s) (hθP T s) (hθQ (OP T) (sP T s)) rfl (hT T) (hsec T s)

end Nine

section One

variable {R : Type u} {ρ : Type w} [CommRing R] [SetLike ρ R] [AddSubgroupClass ρ R]
  (ℛ : ℕ → ρ) [GradedRing ℛ]

/-- **Two sections of a twisting sheaf over two equal opens agree as soon as they agree at every
point**, the first read through the restriction along the equality of opens. Restriction in the
sheaf associated to a graded module reindexes the underlying family of homogeneous fractions and
does nothing else, and this is where that is used. -/
public theorem twist_eq_map_eqToHom (n : ℤ) {T T' : (AlgebraicGeometry.Proj ℛ).Opens}
    (h : T = T') (a : (twistingSheaf ℛ n).val.obj (op T))
    (b : (twistingSheaf ℛ n).val.obj (op T'))
    (hab : ∀ (z : ProjectiveSpectrum ℛ) (hz : z ∈ T') (hz' : z ∈ T),
      a.1 ⟨z, hz'⟩ = b.1 ⟨z, hz⟩) :
    (twistingSheaf ℛ n).val.map (eqToHom (congrArg op h)) a = b := by
  subst h
  refine Eq.trans
    (map_eqToHom_rfl (W := AlgebraicGeometry.Proj ℛ) (twistingSheaf ℛ n) T rfl a) ?_
  exact Subtype.ext (funext fun z => hab z.1 z.2 z.2)

end One

/-! ### The comparison on sections at a point, with the prime free -/

section Two

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- The ideal of the canonical prime of `Proj 𝒜` below a point of the image of `U(ψ)` is the
preimage of the ideal of that point. -/
private theorem basePoint_liftPt_asHomogeneousIdeal (ψ : 𝒜 →+*ᵍ ℬ)
    {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens} (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) :
    (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal =
      (z.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.comap ψ :=
  (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).trans
    (congrArg (fun pt : ProjectiveSpectrum ℬ => pt.asHomogeneousIdeal.comap ψ)
      ((ambientPoint_val 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).trans (liftPt_val 𝒜 ℬ ψ z)))

/-- The canonical prime of `Proj 𝒜` below a point of the image of `r_ψ⁻¹ T` lies in `T`. -/
private theorem basePoint_liftPt_mem (ψ : 𝒜 →+*ᵍ ℬ) (T : (AlgebraicGeometry.Proj 𝒜).Opens)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T))) :
    basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) ∈ T :=
  base_mem_of_mem_preimage (mapHom 𝒜 ℬ ψ) T _ (liftPt_mem 𝒜 ℬ ψ z)

/-- **Tag 01MY's comparison on sections, at a point, with the prime of the source free.** The
value is the fibre comparison applied to the value of the section at that prime.

`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection_val` is this statement at the canonical
prime `basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)`; what is gained by making the prime an argument is that
two readings of one prime never have to meet inside a type. -/
public theorem twistSection_val_of (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 n).val.obj (op T))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)))
    (x : ProjectiveSpectrum 𝒜) (hx : x ∈ T)
    (hxb : basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) = x)
    (hxy : x.asHomogeneousIdeal =
      (z.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.comap ψ) :
    (twistSection 𝒜 ℬ ψ n T a).1 z = fibreMap 𝒜 ℬ ψ x z.1 hxy (a.1 ⟨x, hx⟩) := by
  subst hxb
  exact twistSection_val 𝒜 ℬ ψ n T a z

/-- **Tag 01MY's comparison on a pulled-back section**, with the open of `Proj ℬ` over which the
value is delivered written as the image under the inclusion of the domain of definition. This is
`twistMap_pullbackSectionAt` at the inverse image itself. -/
public theorem twistMap_pullbackSectionOn_eq (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens) (s : (twistingSheaf 𝒜 n).val.obj (op T)) :
    (twistMap 𝒜 ℬ ψ n).val.app (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T))
        (pullbackSectionOn (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n) T s) =
      pullbackSectionAt (mapDomain 𝒜 ℬ ψ).ι (twistingSheaf ℬ n)
        ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)
        (ι_preimage_image 𝒜 ℬ ψ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) (twistSection 𝒜 ℬ ψ n T s) := by
  refine Eq.trans (congrArg ((twistMap 𝒜 ℬ ψ n).val.app (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)))
    (pullbackSectionAt_rfl (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n) T rfl s).symm) ?_
  exact twistMap_pullbackSectionAt 𝒜 ℬ ψ n T rfl
    (ι_preimage_image 𝒜 ℬ ψ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T)) s

end Two

/-! ### The comparison on sections of a composite -/

section Three

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **The comparison on sections of a composite, at a point: it is the composite of the two
comparisons on sections.**

This is the mathematical content of Stacks Tag 01MZ's third assertion. The three primes involved
are the point `z` of `Proj 𝒞`, its image `y` under `r_ψ`, and its image under `r_{ψ∘φ}`; the last
is also the image of `y` under `r_φ`, because the homogeneous ideal of each is the preimage of
that of `z` and `HomogeneousIdeal.comap_comap` identifies the two preimages. With that, the
statement is `fibreMap_comp_apply`. -/
public theorem twistSection_comp_val (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (n : ℤ)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens) (s : (twistingSheaf 𝒜 n).val.obj (op T))
    (z : ProjectiveSpectrum 𝒞)
    (h₁ : z ∈ (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι ''ᵁ (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T))
    (h₃ : z ∈ (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ
      ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)))) :
    (twistSection 𝒜 𝒞 (ψ.comp φ) n T s).1 ⟨z, h₁⟩ =
      (twistSection ℬ 𝒞 ψ n ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T))
        (twistSection 𝒜 ℬ φ n T s)).1 ⟨z, h₃⟩ := by
  let z₁ : ↑((mapDomain 𝒜 𝒞 (ψ.comp φ)).ι ''ᵁ (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T)) := ⟨z, h₁⟩
  let z₃ : ↑((mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ
    ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)))) := ⟨z, h₃⟩
  have hy := basePoint_liftPt_mem ℬ 𝒞 ψ ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)) z₃
  have hx' := basePoint_liftPt_mem 𝒜 ℬ φ T
    (⟨basePoint ℬ 𝒞 ψ (liftPt ℬ 𝒞 ψ z₃), hy⟩ :
      ↑((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)))
  have hx := basePoint_liftPt_mem 𝒜 𝒞 (ψ.comp φ) T z₁
  have hyz := basePoint_liftPt_asHomogeneousIdeal ℬ 𝒞 ψ z₃
  have hxz := basePoint_liftPt_asHomogeneousIdeal 𝒜 𝒞 (ψ.comp φ) z₁
  have hxy' := basePoint_liftPt_asHomogeneousIdeal 𝒜 ℬ φ
    (⟨basePoint ℬ 𝒞 ψ (liftPt ℬ 𝒞 ψ z₃), hy⟩ :
      ↑((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)))
  have hcc : z.asHomogeneousIdeal.comap (ψ.comp φ) =
      (z.asHomogeneousIdeal.comap ψ).comap φ := rfl
  have hxx' : basePoint 𝒜 𝒞 (ψ.comp φ) (liftPt 𝒜 𝒞 (ψ.comp φ) z₁) =
      basePoint 𝒜 ℬ φ (liftPt 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 ψ (liftPt ℬ 𝒞 ψ z₃), hy⟩) :=
    ProjectiveSpectrum.ext (((hxz.trans hcc).trans
      (congrArg (fun I : HomogeneousIdeal ℬ => I.comap φ) hyz.symm)).trans hxy'.symm)
  have hxy : (basePoint 𝒜 𝒞 (ψ.comp φ) (liftPt 𝒜 𝒞 (ψ.comp φ) z₁)).asHomogeneousIdeal =
      (basePoint ℬ 𝒞 ψ (liftPt ℬ 𝒞 ψ z₃)).asHomogeneousIdeal.comap φ :=
    (congrArg (fun pt : ProjectiveSpectrum 𝒜 => pt.asHomogeneousIdeal) hxx').trans hxy'
  refine Eq.trans (twistSection_val_of 𝒜 𝒞 (ψ.comp φ) n T s z₁ _ hx rfl hxz) ?_
  refine Eq.trans ?_ (twistSection_val_of ℬ 𝒞 ψ n
    ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)) (twistSection 𝒜 ℬ φ n T s) z₃ _ hy
    rfl hyz).symm
  refine Eq.trans (fibreMap_comp_apply 𝒜 ℬ 𝒞 φ ψ n _ _ _ z hxx' hxy hxy' hyz hxz s hx hx') ?_
  exact congrArg (fibreMap ℬ 𝒞 ψ _ z hyz)
    (twistSection_val_of 𝒜 ℬ φ n T s ⟨basePoint ℬ 𝒞 ψ (liftPt ℬ 𝒞 ψ z₃), hy⟩ _ hx'
      rfl hxy').symm

/-! ### The canonical isomorphism of Tag 01MZ's first assertion -/

/-- **The canonical isomorphism `V ≅ U(ψ ∘ φ)`**, where `V = r_ψ⁻¹(U(φ))`: the identification of
`V` with its image under `U(ψ).ι` followed by the first assertion of Stacks Tag 01MZ, which says
that that image is the domain of definition of the composite.

A definition rather than a `let` inside the statement of `twistMap_comp`: each of its occurrences
there sits inside one of the nine factors, and zeta-expanding them exhausts the kernel's budget.
See the implementation notes. -/
public def mapDomainCompIso (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).toScheme ≅ (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme :=
  (mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ≪≫
    (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm

/-- **Stacks Tag 01MZ's second assertion, at the canonical isomorphism.** This is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp` with the isomorphism named. -/
public theorem mapDomainCompIso_hom_mapHom (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom ≫ mapHom 𝒜 𝒞 (ψ.comp φ) =
      (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) ≫ mapHom 𝒜 ℬ φ :=
  mapHom_comp 𝒜 ℬ 𝒞 φ ψ

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The canonical isomorphism is compatible with the inclusions of the domains of definition.**
This is `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.compIso_hom_comp_ι` with the
isomorphism named. -/
public theorem mapDomainCompIso_hom_ι (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom ≫ (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι =
      (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι ≫ (mapDomain ℬ 𝒞 ψ).ι :=
  compIso_hom_comp_ι 𝒜 ℬ 𝒞 φ ψ

/-- **The two opens of `Proj 𝒞` that the two sides of Tag 01MZ's twist assertion read over
agree.** This is `image_preimage_eq_of` at the canonical isomorphism, whose two inputs are that
`mapDomainCompIso` is an isomorphism and `AlgebraicGeometry.image_morphismRestrict_preimage`. -/
public theorem image_preimage_mapHom_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (T : (AlgebraicGeometry.Proj 𝒜).Opens) :
    (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι ''ᵁ (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T) =
      (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ
        ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T))) :=
  image_preimage_eq_of (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom (mapHom 𝒜 𝒞 (ψ.comp φ))
    (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) (mapHom 𝒜 ℬ φ)
    (mapDomain 𝒜 ℬ φ).ι (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι (mapHom ℬ 𝒞 ψ)
    (mapDomain ℬ 𝒞 ψ).ι (mapDomainCompIso_hom_mapHom 𝒜 ℬ 𝒞 φ ψ)
    (mapDomainCompIso_hom_ι 𝒜 ℬ 𝒞 φ ψ)
    (iso_image_preimage (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ))
    (image_morphismRestrict_preimage (mapHom ℬ 𝒞 ψ) (mapDomain 𝒜 ℬ φ)) T

/-! ### Tag 01MZ's third assertion -/

/-- **Stacks Tag 01MZ's third assertion, for any triple of morphisms of the shape the tag's first
two assertions produce.**

Three morphisms `q`, `p`, `j` out of one scheme into the three domains of definition, whose
composites with `r_{ψ∘φ}` and `r_φ`, with `U(φ).ι` and `r_ψ`, and with `U(ψ∘φ).ι` and `U(ψ).ι`
agree pairwise, and for which the two opens of `Proj 𝒞` the two sides read over agree: then the
comparison `θ_{ψ∘φ}` pulled back along `q` is `θ_φ` pulled back along `p` followed by `θ_ψ`
pulled back along `j`.

`twistMap_comp` is this at the canonical triple, where the three composite identities are the
tag's own second assertion, `AlgebraicGeometry.morphismRestrict_ι` and `mapDomainCompIso_hom_ι`,
and the identification of opens is `image_preimage_mapHom_comp`. -/
public theorem twistMap_comp_of (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme)
    (p : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) (j : W ⟶ (mapDomain ℬ 𝒞 ψ).toScheme)
    (hq : q ≫ mapHom 𝒜 𝒞 (ψ.comp φ) = p ≫ mapHom 𝒜 ℬ φ)
    (hm : p ≫ (mapDomain 𝒜 ℬ φ).ι = j ≫ mapHom ℬ 𝒞 ψ)
    (ht : q ≫ (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι = j ≫ (mapDomain ℬ 𝒞 ψ).ι)
    (hTT : ∀ T : (AlgebraicGeometry.Proj 𝒜).Opens,
      (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι ''ᵁ (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T) =
        (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ
          ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T)))) :
    (Scheme.Modules.pullbackComp q (mapHom 𝒜 𝒞 (ψ.comp φ))).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback q).map (twistMap 𝒜 𝒞 (ψ.comp φ) n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι).hom.app
          (twistingSheaf 𝒞 n) =
      (Scheme.Modules.pullbackCongr hq).hom.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp p (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback p).map (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp p (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hm).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackComp j (mapHom ℬ 𝒞 ψ)).inv.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullback j).map (twistMap ℬ 𝒞 ψ n) ≫
        (Scheme.Modules.pullbackComp j (mapDomain ℬ 𝒞 ψ).ι).hom.app (twistingSheaf 𝒞 n) ≫
        (Scheme.Modules.pullbackCongr ht).inv.app (twistingSheaf 𝒞 n) :=
  twistComp_hom q (mapHom 𝒜 𝒞 (ψ.comp φ)) (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι
    p (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι j (mapHom ℬ 𝒞 ψ) (mapDomain ℬ 𝒞 ψ).ι
    (twistMap 𝒜 𝒞 (ψ.comp φ) n) (twistMap 𝒜 ℬ φ n) (twistMap ℬ 𝒞 ψ n) hq hm ht
    (fun T => (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι ''ᵁ (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T))
    (fun T => ι_preimage_image 𝒜 𝒞 (ψ.comp φ) (mapHom 𝒜 𝒞 (ψ.comp φ) ⁻¹ᵁ T))
    (fun T s => twistSection 𝒜 𝒞 (ψ.comp φ) n T s)
    (fun T s => twistMap_pullbackSectionOn_eq 𝒜 𝒞 (ψ.comp φ) n T s)
    (fun T => (mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T))
    (fun T => ι_preimage_image 𝒜 ℬ φ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T))
    (fun T s => twistSection 𝒜 ℬ φ n T s)
    (fun T s => twistMap_pullbackSectionOn_eq 𝒜 ℬ φ n T s)
    (fun T' => (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ T'))
    (fun T' => ι_preimage_image ℬ 𝒞 ψ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ T'))
    (fun T' t => twistSection ℬ 𝒞 ψ n T' t)
    (fun T' t => twistMap_pullbackSectionOn_eq ℬ 𝒞 ψ n T' t)
    hTT
    (fun T s => twist_eq_map_eqToHom 𝒞 n (hTT T) (twistSection 𝒜 𝒞 (ψ.comp φ) n T s)
      (twistSection ℬ 𝒞 ψ n ((mapDomain 𝒜 ℬ φ).ι ''ᵁ (mapHom 𝒜 ℬ φ ⁻¹ᵁ T))
        (twistSection 𝒜 ℬ φ n T s))
      (fun z hz hz' => twistSection_comp_val 𝒜 ℬ 𝒞 φ ψ n T s z hz' hz))

/-- **Stacks Project, Tag 01MZ.** *The comparison maps on all twists of a composite compose.*

For homomorphisms `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` of nonnegatively graded rings, write
`V = r_ψ⁻¹(U(φ))` and let `mapDomainCompIso : V ≅ U(ψ ∘ φ)` be the canonical isomorphism supplied
by the first assertion of the tag. Pulled back along it, Tag 01MY's comparison `θ_{ψ∘φ}` on the
`n`-th twist is the comparison `θ_φ` pulled back along the restriction `r_ψ ∣_ U(φ)` followed by
the comparison `θ_ψ` pulled back along the inclusion of `V` — the three identifications of
composites that the nine factors need being the second assertion of the tag
(`mapDomainCompIso_hom_mapHom`), `AlgebraicGeometry.morphismRestrict_ι` and
`mapDomainCompIso_hom_ι`.

**No domain of definition is assumed to be everything**, and `θ` is Tag 01MY's comparison for an
arbitrary homomorphism of nonnegatively graded rings. -/
public theorem twistMap_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (n : ℤ) :
    (Scheme.Modules.pullbackComp (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom
          (mapHom 𝒜 𝒞 (ψ.comp φ))).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom).map
          (twistMap 𝒜 𝒞 (ψ.comp φ) n) ≫
        (Scheme.Modules.pullbackComp (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom
          (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι).hom.app (twistingSheaf 𝒞 n) =
      (Scheme.Modules.pullbackCongr
          (mapDomainCompIso_hom_mapHom 𝒜 ℬ 𝒞 φ ψ)).hom.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)
          (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)).map
          (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)
          (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr
          (morphismRestrict_ι (mapHom ℬ 𝒞 ψ) (mapDomain 𝒜 ℬ φ))).hom.app
            (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι
          (mapHom ℬ 𝒞 ψ)).inv.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullback (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι).map
          (twistMap ℬ 𝒞 ψ n) ≫
        (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι
          (mapDomain ℬ 𝒞 ψ).ι).hom.app (twistingSheaf 𝒞 n) ≫
        (Scheme.Modules.pullbackCongr
          (mapDomainCompIso_hom_ι 𝒜 ℬ 𝒞 φ ψ)).inv.app (twistingSheaf 𝒞 n) :=
  twistMap_comp_of 𝒜 ℬ 𝒞 φ ψ n (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom
    (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι
    (mapDomainCompIso_hom_mapHom 𝒜 ℬ 𝒞 φ ψ)
    (morphismRestrict_ι (mapHom ℬ 𝒞 ψ) (mapDomain 𝒜 ℬ φ))
    (mapDomainCompIso_hom_ι 𝒜 ℬ 𝒞 φ ψ) (image_preimage_mapHom_comp 𝒜 ℬ 𝒞 φ ψ)

end Three

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
