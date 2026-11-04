module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Trivialisation
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Fibre

/-!
# The transposed cocycle of Tag 01MZ, computed on sections

`Stacks.AlgebraicGeometry.ProjTwistCocycle.isCocycle_of_transpose` reduces the third assertion of
Stacks Tag 01MZ, for the restriction maps of a quasi-coherent graded algebra, to an equation
between morphisms **into pushforwards** of the twisting sheaves, in which no inverse image of a
sheaf of modules occurs. This file proves that equation.

Every factor of
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose` is, after
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose_eq`, either Tag 01MY's adjoint
comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap` — which is given on
sections by the fibre comparison — or a presheaf restriction map: the trivialisation of the open
domain by `Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTrivialisation_app`, and the congruence
of pushforwards by `rfl`. Restriction in the sheaf associated to a graded module reindexes a
dependent family of homogeneous fractions and does nothing else, so the whole of `twistTranspose`
evaluates, at a point, to a single application of the fibre comparison: that is
`twistTranspose_app_val`. The cocycle is then the composition law for the fibre comparison,
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.fibreMap_comp_apply`.

## Main results

* `…ProjTwistCocycle.twistTranspose_app_val`: **`twistTranspose` on a section, at a point** — the
  fibre comparison of Tag 01MY applied to the value of the section at the image point. Both the
  membership of the point in the domain of definition and the membership of its image in the open
  are free arguments, so nothing is transported.
* `…ProjTwistCocycle.basePoint_of_section`: the image point, computed through the section of the
  open immersion: it is the base map of the transition morphism.
* `…ProjTwistCocycle.res_eq_comp`: restriction in a quasi-coherent graded algebra is functorial
  as a homomorphism of graded rings. This is
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.resRingHom_comp` promoted from
  the ring homomorphism to the graded one.
* `…ProjTwistCocycle.twistTranspose_comp`: **the transposed cocycle at the level of variables** —
  for a composable pair of homomorphisms of nonnegatively graded rings whose domains of definition
  admit sections of their inclusions, the transposes of Tag 01NO's comparisons compose.
* `…ProjTwistCocycle.twistMap_cocycle`: the untransposed form of the previous item — the
  composition law for Tag 01MY's twist map `…ProjTwistCompare.twistMap` for a pair of
  everywhere-defined homomorphisms, presented by sections of the inclusions of their domains of
  definition. Stacks Tag 01MZ's third assertion has no such restriction, and the unconditional
  statement is `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`, which carries the
  project tag; this is the form in which the composition law enters the chain below.
* `…ProjTwistCocycle.transposed_cocycle`: **the transposed form of Tag 01MZ's third assertion at
  the restriction maps of a quasi-coherent graded algebra**, verbatim the hypothesis `htr` of
  `isCocycle_of_transpose`.
* `…ProjTwistCocycle.isCocycle`: **Tag 01MZ's third assertion for the restriction maps of a
  quasi-coherent graded algebra**, with no hypothesis left.
* `…ProjTwistCocycle.pushNested_comp`: the equation
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp` asks for.
* `…ProjTwistCocycle.isNestedCocycle`: **the nested cocycle of Tag 01NR in every integer
  degree**, which was previously available only in degree one and only conditionally.

## Implementation notes

* **The computation is done on sections and at a point, never on morphisms.** Each of the three
  structural factors is `rfl` on a section — `legComposite_val_app_apply`, and the congruence of
  pushforwards by `…NestedCocycleReduction.pushforwardCongr_app_hom_val_app` — and restriction in
  the associated sheaf is reindexing, so the only non-reflexive steps are the trivialisation and
  the fibre composition law. The warnings recorded in
  `StacksFrontier/AlgebraicGeometry/ProjTwistCocycle/Transpose.lean` about the conversion between
  `(p ≫ ι)_*` and `ι_* p_*` do not arise: that conversion is crossed in the *statement* of
  `twistTranspose_app_val`, where it is free, and no proof below crosses it.
* **Every membership proof is a free argument.** The three readings of the point — through
  `W ⊆ W'`, through `W' ⊆ U`, and through `W ⊆ U` — differ only in a proposition, so supplying
  them as arguments removes every transport except the one genuine identification of points,
  `basePoint_of_section` together with Tag 01NP's transitivity read on
  `AlgebraicGeometry.Scheme.Hom.base`.
* **`isNestedCocycle` applies the reduction to a `fun` at its own call site**, as
  `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistCocycle.lean` instructs: a declaration
  whose hypothesis is the quantified predicate is recorded there as exceeding the elaborator's
  budget at `whnf`.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.TwistBaseChange

namespace Stacks.AlgebraicGeometry.ProjTwistCocycle

universe u

/-! ### Generic readings on sections -/

section Generic

variable {X Z Y : Scheme.{u}}

/-- **Two morphisms of sheaves of modules are equal as soon as they agree on every section over
every open.** -/
public theorem hom_ext_val_app {M N : X.Modules} {a b : M ⟶ N}
    (h : ∀ (T : X.Opens) (s : M.val.obj (op T)),
      a.val.app (op T) s = b.val.app (op T) s) :
    a = b :=
  SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun T =>
    ModuleCat.hom_ext (LinearMap.ext fun s => h T.unop s))

/-- **`legComposite` on a section**: the first leg, the second leg over the inverse image, and
the congruence of pushforwards, by `rfl`. -/
public theorem legComposite_val_app_apply (φ : X ⟶ Z) (ψ : Z ⟶ Y)
    (g : X ⟶ Y) (hg : φ ≫ ψ = g) (M : Y.Modules) (P : Z.Modules) (N : X.Modules)
    (s : M ⟶ (Scheme.Modules.pushforward ψ).obj P)
    (t : P ⟶ (Scheme.Modules.pushforward φ).obj N) (T : Y.Opens)
    (a : M.val.obj (op T)) :
    (legComposite φ ψ g hg M P N s t).val.app (op T) a =
      ((Scheme.Modules.pushforwardCongr hg).hom.app N).val.app (op T)
        (t.val.app (op (ψ ⁻¹ᵁ T)) (s.val.app (op T) a)) := rfl

/-- A section of a morphism is a section on points. -/
private theorem base_apply_of_comp_eq_id {p : X ⟶ Z} {ι : Z ⟶ X} (h : p ≫ ι = 𝟙 X) (y : X) :
    ι.base (p.base y) = y := by
  simpa using congrArg (fun f : X ⟶ X => f.base y) h

end Generic

/-! ### `twistTranspose` on a section, at a point -/

section Graded

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂] [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ)
  (p : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ ψ).toScheme)
  (g : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜)
  (hg : p ≫ mapHom 𝒜 ℬ ψ = g)
  (hpi : p ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ))

omit [AddSubgroupClass σ R₁] [GradedRing 𝒜] in
include hpi in
/-- **A section of the inclusion of the domain of definition makes the graded homomorphism
everywhere defined.** Every point of `Proj ℬ` lies in `U(ψ)`, being the image under the inclusion
of its image under the section. -/
public theorem mem_mapDomain_of_section (y : AlgebraicGeometry.Proj ℬ) :
    y ∈ mapDomain 𝒜 ℬ ψ := by
  have hy := base_apply_of_comp_eq_id hpi y
  exact hy ▸ (p.base y).2

include hg hpi in
/-- **The image point, computed through the section.** For a point of `Proj ℬ` read into the
domain of definition, Tag 01MY's base map is the base map of the transition morphism `g`. The
membership of the point in `U(ψ)` is a free argument: it is a proposition, so which proof is
supplied does not matter. -/
public theorem basePoint_of_section (y : AlgebraicGeometry.Proj ℬ)
    (hm : y ∈ mapDomain 𝒜 ℬ ψ) :
    basePoint 𝒜 ℬ ψ ⟨y, hm⟩ = g.base y := by
  have hy := base_apply_of_comp_eq_id hpi y
  have h1 : (⟨y, hm⟩ : (mapDomain 𝒜 ℬ ψ).toScheme) = p.base y := Subtype.ext hy.symm
  rw [h1, basePoint, ← hg]
  rfl

variable (n : ℤ)

include hg hpi in
/-- **The transpose of Tag 01NO's comparison, read on a section over an arbitrary open and
evaluated at a point.** It is Tag 01MY's fibre comparison at the point, applied to the value of
the section at the image point, and nothing else: the two factors separating them are presheaf
restriction maps, and restriction in the sheaf associated to a graded module reindexes the family
of homogeneous fractions.

Both the membership of the point in the domain of definition and the membership of its image in
the open are free arguments. -/
public theorem twistTranspose_app_val
    (T : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (op T))
    (y : ↥(g ⁻¹ᵁ T)) (hm : (y.1 : AlgebraicGeometry.Proj ℬ) ∈ mapDomain 𝒜 ℬ ψ)
    (hbp : basePoint 𝒜 ℬ ψ ⟨y.1, hm⟩ ∈ T) :
    ((twistTranspose p (mapHom 𝒜 ℬ ψ) (mapDomain 𝒜 ℬ ψ).ι g hg hpi
            (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ ψ n)).val.app (op T) a).1 y =
      twistFibreMap 𝒜 ℬ ψ ⟨y.1, hm⟩ (a.1 ⟨basePoint 𝒜 ℬ ψ ⟨y.1, hm⟩, hbp⟩) := by
  have hstep : (twistTranspose p (mapHom 𝒜 ℬ ψ) (mapDomain 𝒜 ℬ ψ).ι g hg hpi
        (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ ψ n)).val.app (op T) a =
      ((Scheme.Modules.pushforwardCongr hg).hom.app (twistingSheaf ℬ n)).val.app (op T)
        ((twistingSheaf ℬ n).val.map
          (eqToHom (preimage_eq_image p (mapDomain 𝒜 ℬ ψ).ι hpi
            (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T))).op
          ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op T) a)) := by
    rw [twistTranspose_eq]
    refine Eq.trans (legComposite_val_app_apply p (mapHom 𝒜 ℬ ψ) g hg
      (twistingSheaf 𝒜 n)
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))
      (twistingSheaf ℬ n) (twistPushforwardMap 𝒜 ℬ ψ n)
      (twistTrivialisation p (mapDomain 𝒜 ℬ ψ).ι hpi (twistingSheaf ℬ n)) T a) ?_
    exact congrArg _ (twistTrivialisation_val_app_apply p (mapDomain 𝒜 ℬ ψ).ι hpi
      (twistingSheaf ℬ n) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ T) _)
  refine Eq.trans (congrArg (fun z :
      ((Scheme.Modules.pushforward g).obj (twistingSheaf ℬ n)).val.obj (op T) =>
    Subtype.val z y) hstep) ?_
  rfl

end Graded

/-! ### The composition law for the fibre comparison, with the composite homomorphism free -/

section Fibre

universe w w' w''

variable {R₁ R₂ R₃ : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [SetLike σ R₁] [AddSubgroupClass σ R₁] [SetLike τ R₂] [AddSubgroupClass τ R₂]
  [SetLike υ R₃] [AddSubgroupClass υ R₃]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **The composition law for the fibre comparison on a section, with the composite homomorphism
supplied as a variable.** `…ProjTwistCompTwistMap.fibreMap_comp_apply` states it for the literal
composite `χ.comp φ`; at the restriction maps of a quasi-coherent graded algebra the composite
arises as `A.res` of the transitive containment, which is only propositionally that composite. -/
public theorem fibreMap_comp_apply_of (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) (ξ : 𝒜 →+*ᵍ 𝒞)
    (hξ : ξ = χ.comp φ) (n : ℤ) (x x' : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ)
    (z : ProjectiveSpectrum 𝒞) (hxx' : x = x')
    (hxy : x.asHomogeneousIdeal = HomogeneousIdeal.comap φ y.asHomogeneousIdeal)
    (hxy' : x'.asHomogeneousIdeal = HomogeneousIdeal.comap φ y.asHomogeneousIdeal)
    (hyz : y.asHomogeneousIdeal = HomogeneousIdeal.comap χ z.asHomogeneousIdeal)
    (hxz : x.asHomogeneousIdeal = HomogeneousIdeal.comap ξ z.asHomogeneousIdeal)
    {T : (AlgebraicGeometry.Proj 𝒜).Opens} (a : (twistingSheaf 𝒜 n).val.obj (op T))
    (hx : x ∈ T) (hx' : x' ∈ T) :
    fibreMap 𝒜 𝒞 ξ x z hxz (a.1 ⟨x, hx⟩) =
      fibreMap ℬ 𝒞 χ y z hyz (fibreMap 𝒜 ℬ φ x' y hxy' (a.1 ⟨x', hx'⟩)) := by
  subst hξ
  exact ProjTwistCompTwistMap.fibreMap_comp_apply 𝒜 ℬ 𝒞 φ χ n x x' y z hxx' hxy hxy' hyz hxz
    a hx hx'

end Fibre

/-! ### The transposed cocycle, at the level of variables -/

section GradedCocycle

universe w w' w''

variable {R₁ R₂ R₃ : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [SetLike σ R₁] [AddSubgroupClass σ R₁] [SetLike τ R₂] [AddSubgroupClass τ R₂]
  [SetLike υ R₃] [AddSubgroupClass υ R₃]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) (ξ : 𝒜 →+*ᵍ 𝒞) (hξ : ξ = χ.comp φ)
  (pφ : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
  (pχ : AlgebraicGeometry.Proj 𝒞 ⟶ (mapDomain ℬ 𝒞 χ).toScheme)
  (pξ : AlgebraicGeometry.Proj 𝒞 ⟶ (mapDomain 𝒜 𝒞 ξ).toScheme)
  (gφ : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜)
  (gχ : AlgebraicGeometry.Proj 𝒞 ⟶ AlgebraicGeometry.Proj ℬ)
  (gξ : AlgebraicGeometry.Proj 𝒞 ⟶ AlgebraicGeometry.Proj 𝒜)
  (hgφ : pφ ≫ mapHom 𝒜 ℬ φ = gφ) (hgχ : pχ ≫ mapHom ℬ 𝒞 χ = gχ)
  (hgξ : pξ ≫ mapHom 𝒜 𝒞 ξ = gξ)
  (hpiφ : pφ ≫ (mapDomain 𝒜 ℬ φ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ))
  (hpiχ : pχ ≫ (mapDomain ℬ 𝒞 χ).ι = 𝟙 (AlgebraicGeometry.Proj 𝒞))
  (hpiξ : pξ ≫ (mapDomain 𝒜 𝒞 ξ).ι = 𝟙 (AlgebraicGeometry.Proj 𝒞))
  (hcomp : gχ ≫ gφ = gξ) (n : ℤ)

include hξ hgφ hgχ hgξ hpiφ hpiχ hpiξ hcomp in
/-- **The transposed form of Tag 01MZ's third assertion, at the level of variables.** For a
composable pair of homomorphisms of nonnegatively graded rings, each of whose domains of
definition admits a section of its inclusion, the transposes of Tag 01NO's comparisons compose.

The proof is a pointwise computation. By `twistTranspose_app_val` each of the three transposes
is, on a section at a point, one application of Tag 01MY's fibre comparison; the three points are
matched by `basePoint_of_section` together with the transitivity `hcomp` read on
`AlgebraicGeometry.Scheme.Hom.base`, and the equation that remains is the composition law for the
fibre comparison, `fibreMap_comp_apply_of`. -/
public theorem twistTranspose_comp :
    legComposite gχ gφ gξ hcomp (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistingSheaf 𝒞 n)
        (twistTranspose pφ (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι gφ hgφ hpiφ
          (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ φ n))
        (twistTranspose pχ (mapHom ℬ 𝒞 χ) (mapDomain ℬ 𝒞 χ).ι gχ hgχ hpiχ
          (twistingSheaf ℬ n) (twistingSheaf 𝒞 n) (twistMap ℬ 𝒞 χ n)) =
      twistTranspose pξ (mapHom 𝒜 𝒞 ξ) (mapDomain 𝒜 𝒞 ξ).ι gξ hgξ hpiξ
        (twistingSheaf 𝒜 n) (twistingSheaf 𝒞 n) (twistMap 𝒜 𝒞 ξ n) := by
  refine hom_ext_val_app fun T a => ?_
  refine Subtype.ext (funext fun y => ?_)
  -- The point of `Proj 𝒞`, read into each of the three domains of definition.
  have hmχ := mem_mapDomain_of_section ℬ 𝒞 χ pχ hpiχ y.1
  have hmξ := mem_mapDomain_of_section 𝒜 𝒞 ξ pξ hpiξ y.1
  have hbχ : basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩ = gχ.base y.1 :=
    basePoint_of_section ℬ 𝒞 χ pχ gχ hgχ hpiχ y.1 hmχ
  have hbξ : basePoint 𝒜 𝒞 ξ ⟨y.1, hmξ⟩ = gξ.base y.1 :=
    basePoint_of_section 𝒜 𝒞 ξ pξ gξ hgξ hpiξ y.1 hmξ
  have hmφ := mem_mapDomain_of_section 𝒜 ℬ φ pφ hpiφ (basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩)
  have hbφ : basePoint 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩ =
      gφ.base (basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩) :=
    basePoint_of_section 𝒜 ℬ φ pφ gφ hgφ hpiφ _ hmφ
  -- The two readings of the image point in `Proj 𝒜` agree: this is `hcomp` on base maps.
  have hbase : ∀ z : AlgebraicGeometry.Proj 𝒞, gξ.base z = gφ.base (gχ.base z) := fun z => by
    have h := congrArg (fun f : AlgebraicGeometry.Proj 𝒞 ⟶ AlgebraicGeometry.Proj 𝒜 =>
      f.base z) hcomp
    simpa using h.symm
  have hpt : basePoint 𝒜 𝒞 ξ ⟨y.1, hmξ⟩ =
      basePoint 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩ :=
    (hbξ.trans ((hbase y.1).trans
      (congrArg (fun z : AlgebraicGeometry.Proj ℬ => gφ.base z) hbχ.symm))).trans hbφ.symm
  -- The memberships in the opens.
  have hbpξ : basePoint 𝒜 𝒞 ξ ⟨y.1, hmξ⟩ ∈ T := hbξ ▸ y.2
  have hbpφ : basePoint 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩ ∈ T := hpt ▸ hbpξ
  have hbpχ : basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩ ∈ gφ ⁻¹ᵁ T := by
    have h : gφ.base (basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩) ∈ T := hbφ ▸ hbpφ
    exact h
  have hopen : (gξ ⁻¹ᵁ T : (AlgebraicGeometry.Proj 𝒞).Opens) = gχ ⁻¹ᵁ (gφ ⁻¹ᵁ T) := by
    rw [← hcomp]; rfl
  have hyin : (y.1 : AlgebraicGeometry.Proj 𝒞) ∈ gχ ⁻¹ᵁ (gφ ⁻¹ᵁ T) := hopen ▸ y.2
  -- The three transposes on the section, at the point.
  have hL := legComposite_val_app_apply gχ gφ gξ hcomp (twistingSheaf 𝒜 n)
    (twistingSheaf ℬ n) (twistingSheaf 𝒞 n)
    (twistTranspose pφ (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι gφ hgφ hpiφ
      (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ φ n))
    (twistTranspose pχ (mapHom ℬ 𝒞 χ) (mapDomain ℬ 𝒞 χ).ι gχ hgχ hpiχ
      (twistingSheaf ℬ n) (twistingSheaf 𝒞 n) (twistMap ℬ 𝒞 χ n)) T a
  have hχval := twistTranspose_app_val ℬ 𝒞 χ pχ gχ hgχ hpiχ n (gφ ⁻¹ᵁ T)
    ((twistTranspose pφ (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι gφ hgφ hpiφ
      (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ φ n)).val.app (op T) a)
    ⟨y.1, hyin⟩ hmχ hbpχ
  have hφval := twistTranspose_app_val 𝒜 ℬ φ pφ gφ hgφ hpiφ n T a
    ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hbpχ⟩ hmφ hbpφ
  have hξval := twistTranspose_app_val 𝒜 𝒞 ξ pξ gξ hgξ hpiξ n T a y hmξ hbpξ
  refine Eq.trans (congrArg (fun z :
      ((Scheme.Modules.pushforward gξ).obj (twistingSheaf 𝒞 n)).val.obj (op T) =>
    Subtype.val z y) hL) ?_
  refine Eq.trans hχval ?_
  refine Eq.trans (congrArg (fun c => twistFibreMap ℬ 𝒞 χ ⟨y.1, hmχ⟩ c) hφval) ?_
  refine Eq.trans ?_ hξval.symm
  refine (fibreMap_comp_apply_of 𝒜 ℬ 𝒞 φ χ ξ hξ n
    (basePoint 𝒜 𝒞 ξ ⟨y.1, hmξ⟩)
    (basePoint 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩)
    (basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩) y.1 hpt ?_
    (basePoint_asHomogeneousIdeal 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩)
    (basePoint_asHomogeneousIdeal ℬ 𝒞 χ ⟨y.1, hmχ⟩)
    (basePoint_asHomogeneousIdeal 𝒜 𝒞 ξ ⟨y.1, hmξ⟩) a hbpξ hbpφ).symm
  exact hpt ▸ basePoint_asHomogeneousIdeal 𝒜 ℬ φ ⟨basePoint ℬ 𝒞 χ ⟨y.1, hmχ⟩, hmφ⟩

include hξ hgφ hgχ hgξ hpiφ hpiχ hpiξ hcomp in
/-- **The comparison maps on all twists of a composite compose**, for a composable pair of
homomorphisms of nonnegatively graded rings each of whose domains of definition is the whole
projective spectrum — presented, as everywhere in this chain, by a section `p` of the inclusion
of that domain.

This is the form in which the composition law enters the chain of this file, and it is **not**
Stacks Tag 01MZ's third assertion, which has no everywhere-definedness restriction: that is
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`, where the two sides are read on
`U(ψ ∘ φ)` through the canonical isomorphism of the tag's first assertion, and it is there that
the project tag sits. No attribute is attached here.

Each of Tag 01NO's comparisons is the six-factor composite of
`Stacks.AlgebraicGeometry.ProjTwistCocycle.transpose_sixFold`: the congruence for the
factorisation `p ≫ r = g`, the pseudofunctoriality isomorphism, the inverse image along `p` of Tag
01MY's twist map `…ProjTwistCompare.twistMap`, and the trivialisation of the open domain. The
equation is the untransposed form of `twistTranspose_comp`, obtained from it by
`hom_ext_of_transpose`: the transpose is a bijection, and `transpose_legComp` together with
`transpose_sixFold` identifies the transpose of each side. -/
public theorem twistMap_cocycle :
    (Scheme.Modules.pullbackCongr hcomp).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp gχ gφ).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback gχ).map
          ((Scheme.Modules.pullbackCongr hgφ).inv.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullbackComp pφ (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullback pφ).map (twistMap 𝒜 ℬ φ n) ≫
            (Scheme.Modules.pullbackComp pφ (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackCongr hpiφ).hom.app (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
              (twistingSheaf ℬ n)) ≫
        ((Scheme.Modules.pullbackCongr hgχ).inv.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackComp pχ (mapHom ℬ 𝒞 χ)).inv.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullback pχ).map (twistMap ℬ 𝒞 χ n) ≫
          (Scheme.Modules.pullbackComp pχ (mapDomain ℬ 𝒞 χ).ι).hom.app (twistingSheaf 𝒞 n) ≫
          (Scheme.Modules.pullbackCongr hpiχ).hom.app (twistingSheaf 𝒞 n) ≫
          (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj 𝒞)).hom.app
            (twistingSheaf 𝒞 n)) =
      (Scheme.Modules.pullbackCongr hgξ).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp pξ (mapHom 𝒜 𝒞 ξ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback pξ).map (twistMap 𝒜 𝒞 ξ n) ≫
        (Scheme.Modules.pullbackComp pξ (mapDomain 𝒜 𝒞 ξ).ι).hom.app (twistingSheaf 𝒞 n) ≫
        (Scheme.Modules.pullbackCongr hpiξ).hom.app (twistingSheaf 𝒞 n) ≫
        (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj 𝒞)).hom.app (twistingSheaf 𝒞 n) := by
  refine hom_ext_of_transpose (Scheme.Modules.pullbackPushforwardAdjunction gξ) ?_
  refine Eq.trans (transpose_legComp gχ gφ gξ hcomp (twistingSheaf 𝒜 n) (twistingSheaf ℬ n)
    (twistingSheaf 𝒞 n) _ _) ?_
  refine Eq.trans (legTranspose_eq_legComposite gχ gφ gξ hcomp (twistingSheaf 𝒜 n)
    (twistingSheaf ℬ n) (twistingSheaf 𝒞 n) _ _) ?_
  rw [transpose_sixFold pφ (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι gφ hgφ hpiφ
      (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ φ n),
    transpose_sixFold pχ (mapHom ℬ 𝒞 χ) (mapDomain ℬ 𝒞 χ).ι gχ hgχ hpiχ
      (twistingSheaf ℬ n) (twistingSheaf 𝒞 n) (twistMap ℬ 𝒞 χ n)]
  refine Eq.trans (twistTranspose_comp 𝒜 ℬ 𝒞 φ χ ξ hξ pφ pχ pξ gφ gχ gξ hgφ hgχ hgξ
    hpiφ hpiχ hpiξ hcomp n) ?_
  exact (transpose_sixFold pξ (mapHom 𝒜 𝒞 ξ) (mapDomain 𝒜 𝒞 ξ).ι gξ hgξ hpiξ
    (twistingSheaf 𝒜 n) (twistingSheaf 𝒞 n) (twistMap 𝒜 𝒞 ξ n)).symm

end GradedCocycle

/-! ### Restriction in a quasi-coherent graded algebra is functorial -/

section Res

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **Restriction of the graded rings of sections is functorial as a homomorphism of graded
rings.** `…SheafGradedAlgebra.resRingHom_comp` is the same statement for the underlying ring
homomorphism, and the graded homomorphism carries no further data. The containment of the outer
pair is a free argument. -/
public theorem res_eq_comp {W W' U : S.Opens} (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) :
    A.res hWU = (A.res hWW').comp (A.res hW'U) := by
  refine GradedRingHom.ext fun x => ?_
  have h : A.resRingHom hWU = (A.resRingHom hWW').comp (A.resRingHom hW'U) :=
    A.resRingHom_comp hWW' hW'U
  exact congrArg (fun f : A.sectionRing U →+* A.sectionRing W => f x) h

end Res

/-! ### The instance: the restriction maps of a quasi-coherent graded algebra -/

section Instance

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (n : ℤ) (W W' U : S.Opens)
  (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
  (hU : IsAffineOpen U)

/-- **The transposed form of Tag 01MZ's third assertion for the restriction maps of a
quasi-coherent graded algebra.** This is verbatim the hypothesis `htr` of
`isCocycle_of_transpose`, and it is `twistTranspose_comp` at the three restriction maps of a chain
`W ⊆ W' ⊆ U` of affine opens: their transition morphisms are
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap`, each factors through the identification
of the open domain with the whole projective spectrum
(`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap_eq_comp`), that identification is a
section of the inclusion (`…projInclusionTopSection_ι`), and the restriction maps compose by
`res_eq_comp`. -/
public theorem transposed_cocycle :
    legComposite (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (ChartTransRelativeProj.projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
        (twistingSheaf (A.grading W) n)
        (twistTranspose (projInclusionTopSection A W' U hW'U hW' hU)
          (projMapData (A.grading U) (A.grading W') (A.res hW'U)).hom
          (mapDomain (A.grading U) (A.grading W') (A.res hW'U)).ι
          (projInclusionMap A W' U hW'U hW' hU)
          (projInclusionMap_eq_comp A W' U hW'U hW' hU)
          (projInclusionTopSection_ι A W' U hW'U hW' hU)
          (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
          ((projMapData (A.grading U) (A.grading W') (A.res hW'U)).twistMap n))
        (twistTranspose (projInclusionTopSection A W W' hWW' hW hW')
          (projMapData (A.grading W') (A.grading W) (A.res hWW')).hom
          (mapDomain (A.grading W') (A.grading W) (A.res hWW')).ι
          (projInclusionMap A W W' hWW' hW hW')
          (projInclusionMap_eq_comp A W W' hWW' hW hW')
          (projInclusionTopSection_ι A W W' hWW' hW hW')
          (twistingSheaf (A.grading W') n) (twistingSheaf (A.grading W) n)
          ((projMapData (A.grading W') (A.grading W) (A.res hWW')).twistMap n)) =
      twistTranspose (projInclusionTopSection A W U hWU hW hU)
        (projMapData (A.grading U) (A.grading W) (A.res hWU)).hom
        (mapDomain (A.grading U) (A.grading W) (A.res hWU)).ι
        (projInclusionMap A W U hWU hW hU) (projInclusionMap_eq_comp A W U hWU hW hU)
        (projInclusionTopSection_ι A W U hWU hW hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W) n)
        ((projMapData (A.grading U) (A.grading W) (A.res hWU)).twistMap n) :=
  twistTranspose_comp (A.grading U) (A.grading W') (A.grading W)
    (A.res hW'U) (A.res hWW') (A.res hWU) (res_eq_comp A hWW' hW'U hWU)
    (projInclusionTopSection A W' U hW'U hW' hU)
    (projInclusionTopSection A W W' hWW' hW hW')
    (projInclusionTopSection A W U hWU hW hU)
    (projInclusionMap A W' U hW'U hW' hU)
    (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W U hWU hW hU)
    (projInclusionMap_eq_comp A W' U hW'U hW' hU)
    (projInclusionMap_eq_comp A W W' hWW' hW hW')
    (projInclusionMap_eq_comp A W U hWU hW hU)
    (projInclusionTopSection_ι A W' U hW'U hW' hU)
    (projInclusionTopSection_ι A W W' hWW' hW hW')
    (projInclusionTopSection_ι A W U hWU hW hU)
    (ChartTransRelativeProj.projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU) n

/-- **Stacks Tag 01MZ's third assertion for the restriction maps of a quasi-coherent graded
algebra**: the canonical comparison isomorphisms on the `n`-th twist compose along a chain
`W ⊆ W' ⊆ U` of affine opens of the base.

This is `isCocycle_of_transpose` with its hypothesis discharged by `transposed_cocycle`, and it is
the equation `…ChartTransRelativeProj.pushNested_comp_of` asks for. -/
public theorem isCocycle :
    (Scheme.Modules.pullbackCongr
            (ChartTransRelativeProj.projInclusionMap_comp'
              A W W' U hWW' hW'U hWU hW hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackComp (projInclusionMap A W W' hWW' hW hW')
            (projInclusionMap A W' U hW'U hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullback (projInclusionMap A W W' hWW' hW hW')).map
          (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom ≫
        (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom =
      (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n).hom :=
  isCocycle_of_transpose A n W W' U hWW' hW'U hWU hW hW' hU
    (transposed_cocycle A n W W' U hWW' hW'U hWU hW hW' hU)

/-- **The composition law for the pushed-forward comparison on the relative projective
spectrum**, which is what `…ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp` consumes.
It is `…ChartTransRelativeProj.pushNested_comp_of` with its cocycle hypothesis discharged by
`isCocycle`. -/
public theorem pushNested_comp :
    ChartTransRelativeProj.pushNested A W' U hW'U hW' hU n ≫
        ChartTransRelativeProj.pushNested A W W' hWW' hW hW' n =
      ChartTransRelativeProj.pushNested A W U hWU hW hU n :=
  ChartTransRelativeProj.pushNested_comp_of A n W W' U hWW' hW'U hWU hW hW' hU
    (isCocycle A n W W' U hWW' hW'U hWU hW hW' hU)

end Instance

/-! ### The nested cocycle -/

section Nested

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (n : ℤ)

/-- **The nested cocycle of Tag 01NR, in every integer degree.** Previously this was available
only in degree one, and only on an additional rigidity hypothesis
(`…ChartCocycleRigidity.isNestedCocycle_one`); it is here unconditional and in every degree.

The reduction is applied to a `fun` built from `pushNested_comp` at this call site, as
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistCocycle.lean` instructs: a declaration
whose hypothesis is the quantified predicate is recorded there as exceeding the elaborator's
budget at `whnf`.

No `stacks` attribute is attached here. `IsNestedCocycle` is a cocycle for
`…ChartTransRelativeProj.cmpNested` over a chain of affine opens of the base, read on sections,
and `StacksFrontier/AlgebraicGeometry/ProjTwistCompFunctoriality/Basic.lean` records that this is
**not** Tag 01MZ's third assertion, which is a composition law for
`…ProjTwistCompare.twistMap` over composable graded ring maps. That assertion is
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`, which carries its tag; this is
its consequence on the relative projective spectrum, and the input of Tag 01NR. -/
public theorem isNestedCocycle : ChartTransRelativeProj.IsNestedCocycle A n :=
  ChartTransRelativeProj.isNestedCocycle_of_pushNested_comp A n
    fun W W' U hWW' hW'U hWU hW hW' hU =>
      pushNested_comp A n W W' U hWW' hW'U hWU hW hW' hU

end Nested

end Stacks.AlgebraicGeometry.ProjTwistCocycle

end
