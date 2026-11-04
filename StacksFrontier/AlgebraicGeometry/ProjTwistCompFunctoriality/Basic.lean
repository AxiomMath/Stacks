module

public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.General
public import StacksFrontier.AlgebraicGeometry.ProjMapComposition.Basic
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn

/-!
# Functoriality of Tag 01MY's comparison on twists: the inputs, and where the kernel stops

Tag 01MZ has three assertions about a composite `ψ ∘ φ` of homomorphisms of nonnegatively
graded rings: that the domain of definition of the composite is the image under `U(ψ).ι` of
`V = r_ψ⁻¹(U(φ))`, that the induced scheme morphisms compose, and that the comparison maps `θ`
on every twist compose. The first two are proved and tagged
(`Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_comp` and
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_comp`). The third is the subject of this file,
and it is **not** proved here: what is proved is the composition law on *fibres*, together with
the generic machinery any route to the sheaf-level statement needs, and the obstruction that
stops the sheaf-level statement is recorded below.

That third assertion is also the input `Stacks.AlgebraicGeometry.NestedCocycleTail.IsChartCocycle`
needs — the owning file says so at `NestedCocycleTail/Basic.lean:56-59`, where the chart cocycle
is described as this functoriality "transported across six pullback factors". The two statements
are **not** the same statement: `IsChartCocycle` is a cocycle for
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` over a chain `W ⊆ W' ⊆ U` of
affine opens of a base scheme, read on sections, while Tag 01MZ's assertion is a composition law
for `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` over composable graded ring maps.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.inclPt`: a point of a smaller open of a
  scheme, read as a point of a bigger one.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.outerPt`: a point of the domain of
  definition of the composite, read as a point of the domain of definition of `ψ`.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.innerPt`: its image under `r_ψ`, read as
  a point of the domain of definition of `φ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.hom_ext_of_pullbackSectionOn`: **two
  morphisms out of an inverse image agree as soon as they agree on pulled-back sections**, over
  every open. This is the bijectivity of `CategoryTheory.Adjunction.homEquiv` read on
  components, and it is the reduction that turns an equation between composites of
  pseudofunctoriality isomorphisms into an equation between sections.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.pullbackCongr_hom_pullbackSectionOn` and
  `pullbackCongr_inv_pullbackSectionOn`: **the congruence isomorphism of two equal morphisms on
  a pulled-back section, over an arbitrary open**, with the identification of the two inverse
  images carried by an `CategoryTheory.eqToHom` of opens.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.basePoint_comp_asHomogeneousIdeal`: the
  homogeneous ideal at the image of a point under the composite is the `φ`-preimage of the one
  at its image under `r_ψ`.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.basePoint_innerPt`: the two readings of
  that image point — through the composite, and through `r_ψ` followed by `r_φ` — are the same
  point of `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.twistFibreMap_eq_comp`: **the
  composition law for the comparison on fibres**, which is the mathematical content of Tag
  01MZ's twist assertion. The intermediate homogeneous prime is a free argument, so the
  statement mentions only one point of `Proj 𝒞` and needs no transport.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.fibreMap_apply_congr`: **the transport
  that identifies the two readings of a section at two equal points**, which is what composing
  two comparisons on sections needs.
* `Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.compIso_hom_comp_ι`: the identity Tag
  01MZ's twist assertion feeds to the last of its nine factors.

## What this file does not carry, and the measurement that shaped the route

**No `stacks` attribute is attached to any declaration in this file. Nothing here is a covering
set for any label.** Tag 01MZ's `the maps on all twists of the composite` is an equation between
a three-factor and a nine-factor composite of components of the pseudofunctoriality isomorphisms
of the inverse image, and only its innermost factor is supplied here; the assertion itself is
discharged in `StacksFrontier/AlgebraicGeometry/ProjTwistCompTwistMap/Comp.lean`, as
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp`, by the cure this file's last
paragraph proposes — every step pushed to the level of variables, with
`twistFibreMap_eq_comp`'s free intermediate prime as the model.

The statement itself is affordable — it elaborates and type-checks with the two proved assertions of
Tag 01MZ supplying its `hq` and `hm`, and `compIso_hom_comp_ι` its `ht`. What the direct routes
cannot take is one step inside, and it is a **kernel** cost rather than a missing input:

> `((⟨w.1, h⟩ : (mapDomain ℬ 𝒞 ψ).toScheme).1 : AlgebraicGeometry.Proj 𝒞) = w.1`,
> a single projection on a structure literal, is a **`(kernel) deterministic timeout`** when
> `w` ranges over `(mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme`.

The reason is that the kernel must put `↥((mapDomain ℬ 𝒞 ψ).toScheme)` in weak head normal form
before it can project, and that unfolds the open-subscheme construction over `Proj 𝒞`. With the
graded rings as variables it is still too expensive, and the composite `ψ.comp φ` inside the
other open makes it worse. Every such step in this file is therefore routed through a lemma
proved **at the level of variable opens** — `inclPt_val`, `projInclPt_val`, `ambientPoint_val`,
`projMk_val` — where the same `rfl` costs nothing, and instantiating those lemmas performs
substitution and demands no reduction. That technique is what makes the declarations below
possible at all, and it is the same discipline `ProjInclusionTwist.projInclusionTwistMap_eq` and
`PullbackUnit.pullbackCongr_refl_inv_app` were forced into.

It does not suffice by itself for the step above the fibre level, and the
residue is stated exactly: the two sides of Tag 01MZ's assertion read the section at the two
points `basePoint 𝒜 ℬ φ (innerPt w)` and `basePoint 𝒜 𝒞 (ψ.comp φ) w` of `Proj 𝒜`, which
`basePoint_innerPt` shows are equal but not definitionally so, and the fibre a section takes its
value in depends on the point. So composing the comparison on sections of `φ` with that of `ψ`
produces a value whose type is indexed by one spelling of a point of `Proj 𝒞` while the
composite's value is indexed by another, and making those two types meet is the projection the
kernel refuses. The free-intermediate-point form `twistFibreMap_eq_comp` and the transport
`fibreMap_apply_congr` are how this file keeps that identification out of every type it writes.

**That residue yields to the same cure.** Pushing the whole comparison-on-sections
composition into statements at the level of variable schemes, variable opens and variable
sheaves — so that the concrete `mapDomain`s enter only by substitution — is what
`Stacks.AlgebraicGeometry.TwistMultCompat` did for the companion label of Tag 01NO, whose
residue had been recorded in the same terms, and it is what
`StacksFrontier/AlgebraicGeometry/ProjTwistCompTwistMap/` does for this one: the nine factors are
evaluated on a pulled-back section with every scheme and every open a variable, and the three
morphisms out of `r_ψ⁻¹(U(φ))` are universally quantified and instantiated only in the last
statement.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.TwistBaseChange

namespace Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality

universe u w w' w''

/-! ### Generic lemmas about points of opens and about pulled-back sections

Every `rfl` in this file is taken here, with the scheme and the opens variables. At a concrete
`Stacks.AlgebraicGeometry.ProjShared.mapDomain` the same `rfl` is a kernel timeout; see the
module docstring. -/

section Generic

variable {X Y : Scheme.{u}}

/-- **A point of a smaller open, read as a point of a bigger one.** -/
public def inclPt {U V : X.Opens} (h : U ≤ V) (w : U.toScheme) : V.toScheme := ⟨w.1, h w.2⟩

/-- `inclPt` does not move the underlying point of the ambient scheme. -/
public theorem inclPt_val {U V : X.Opens} (h : U ≤ V) (w : U.toScheme) :
    ((inclPt h w).1 : X) = w.1 := rfl

/-- The underlying point of a point of an open written as a structure literal. -/
public theorem mk_val {V : X.Opens} (p : X) (h : p ∈ V) :
    (((⟨p, h⟩ : V.toScheme)).1 : X) = p := rfl

/-- Membership in an inverse image, read as membership of the image point. -/
public theorem base_mem_of_mem_preimage (f : X ⟶ Y) (U : Y.Opens) (x : X) (h : x ∈ f ⁻¹ᵁ U) :
    f.base x ∈ U := h

/-- Membership in the inverse image along the inclusion of an open, read on the underlying
point. -/
public theorem mem_preimage_ι {U : X.Opens} (W : X.Opens) (w : U.toScheme)
    (h : (w.1 : X) ∈ W) : w ∈ U.ι ⁻¹ᵁ W := h

/-- **Two morphisms out of an inverse image agree as soon as they agree on pulled-back
sections.**

A morphism `f^*M ⟶ N` is the same thing as a morphism `M ⟶ f_*N` by
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, and the transpose of `α` is
`T ↦ α` applied to `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn f M T`. So the
hypothesis says exactly that the two transposes have the same components, and
`CategoryTheory.Adjunction.homEquiv` is injective.

This is the reduction an equation between composites of the pseudofunctoriality isomorphisms of
the inverse image needs: each factor's action on a pulled-back section is computed by one of the
lemmas of `Stacks.AlgebraicGeometry.PullbackUnit`, whereas the composites themselves cannot be
compared directly. -/
public theorem hom_ext_of_pullbackSectionOn {f : X ⟶ Y} {M : Y.Modules} {N : X.Modules}
    (α β : (Scheme.Modules.pullback f).obj M ⟶ N)
    (h : ∀ (T : Y.Opens) (s : M.val.obj (op T)),
      α.val.app (op (f ⁻¹ᵁ T)) (pullbackSectionOn f M T s) =
        β.val.app (op (f ⁻¹ᵁ T)) (pullbackSectionOn f M T s)) :
    α = β := by
  have key : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N α =
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N β := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
    exact ModuleCat.hom_ext (LinearMap.ext fun s => h T.unop s)
  exact (Equiv.apply_eq_iff_eq _).mp key

/-- **The congruence isomorphism of two equal morphisms, on a pulled-back section over an
arbitrary open**, in the `hom` direction.

`Stacks.AlgebraicGeometry.PullbackUnit.pullbackCongr_refl_hom_app` covers the case of a
congruence between a morphism and itself, and the companion file records that the general
statement "cannot be written down" at an arbitrary open, because the two pulled-back sections
live over the propositionally-but-not-definitionally equal opens `f ⁻¹ᵁ T` and `g ⁻¹ᵁ T`. It can
be written down with that identification supplied as an `CategoryTheory.eqToHom` of opens, which
is what this does; the proof is the reflexive case after `subst`. -/
public theorem pullbackCongr_hom_pullbackSectionOn {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (T : Y.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op (f ⁻¹ᵁ T))
        (pullbackSectionOn f M T s) =
      ((Scheme.Modules.pullback g).obj M).val.map
          (eqToHom (congrArg (fun k : X ⟶ Y => op (k ⁻¹ᵁ T)) hf.symm))
        (pullbackSectionOn g M T s) := by
  subst hf
  rw [pullbackCongr_refl_hom_app]
  simp

/-- The same in the `inv` direction. -/
public theorem pullbackCongr_inv_pullbackSectionOn {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (T : Y.Opens) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackCongr hf).inv.app M).val.app (op (g ⁻¹ᵁ T))
        (pullbackSectionOn g M T s) =
      ((Scheme.Modules.pullback f).obj M).val.map
          (eqToHom (congrArg (fun k : X ⟶ Y => op (k ⁻¹ᵁ T)) hf))
        (pullbackSectionOn f M T s) := by
  subst hf
  rw [pullbackCongr_refl_inv_app]
  simp

end Generic

/-! ### The same, at a projective spectrum

`Stacks.AlgebraicGeometry.ProjTwistCompare.ambientPoint` reads the underlying point of a point
of a domain of definition as a relevant homogeneous prime, and that identification is not free
to the kernel either at a concrete open. The two lemmas below take it once, with the graded ring
and the opens variables. -/

section GenericProj

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {R : Type u} {ρ : Type w} [CommRing R] [SetLike ρ R] [AddSubgroupClass ρ R]
  (ℛ : ℕ → ρ) [GradedRing ℛ]

/-- `inclPt_val` read at a projective spectrum. -/
public theorem projInclPt_val {U V : (AlgebraicGeometry.Proj ℛ).Opens} (h : U ≤ V)
    (w : U.toScheme) : ((inclPt h w).1 : ProjectiveSpectrum ℛ) = w.1 := rfl

/-- `mk_val` read at a projective spectrum. -/
public theorem projMk_val {V : (AlgebraicGeometry.Proj ℛ).Opens} (p : ProjectiveSpectrum ℛ)
    (h : p ∈ V) : (((⟨p, h⟩ : V.toScheme)).1 : ProjectiveSpectrum ℛ) = p := rfl

end GenericProj

section AmbientPoint

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `Stacks.AlgebraicGeometry.ProjTwistCompare.ambientPoint` is the underlying point. -/
public theorem ambientPoint_val (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ambientPoint 𝒜 ℬ ψ y = (y.1 : ProjectiveSpectrum ℬ) := rfl

/-- **The value of a section of a twisting sheaf read at two equal points, compared through the
fibre comparison.** The fibre a section takes its value in depends on the point, so reading one
section at two equal-but-not-definitionally-equal points of an open produces values in two
different types; this is the transport that identifies them, and it is stated with both points
and both local-fraction witnesses as variables, which is the only place it is affordable. The
two hypotheses relating the points to `y` are propositions, so which one is supplied does not
matter.

Both readings occur in Tag 01MZ's assertion about the maps on all twists: its two sides read the
section at `basePoint 𝒜 ℬ φ (innerPt w)` and at `basePoint 𝒜 𝒞 (ψ.comp φ) w`, which
`Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality.basePoint_innerPt` shows are the same
point. -/
public theorem fibreMap_apply_congr (ξ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    {T : (AlgebraicGeometry.Proj 𝒜).Opens} (a : (twistingSheaf 𝒜 n).val.obj (op T))
    (x x' : ProjectiveSpectrum 𝒜) (hx : x ∈ T) (hx' : x' ∈ T) (h : x = x')
    (y : ProjectiveSpectrum ℬ)
    (e : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ξ)
    (e' : x'.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ξ) :
    fibreMap 𝒜 ℬ ξ x y e (a.1 ⟨x, hx⟩) = fibreMap 𝒜 ℬ ξ x' y e' (a.1 ⟨x', hx'⟩) := by
  subst h
  rfl

end AmbientPoint

/-! ### The composite situation -/

section Comp

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)

/-- **A point of the domain of definition of the composite, as a point of the domain of
definition of the outer homomorphism.** The containment is
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_comp_le`. -/
public def outerPt (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) : (mapDomain ℬ 𝒞 ψ).toScheme :=
  inclPt (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ) w

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- `outerPt` does not move the underlying point of the ambient projective spectrum. -/
public theorem outerPt_val (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    ((outerPt 𝒜 ℬ 𝒞 φ ψ w).1 : AlgebraicGeometry.Proj 𝒞) = w.1 :=
  inclPt_val (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ) w

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- `outerPt` does not move the underlying relevant homogeneous prime. -/
public theorem ambientPoint_outerPt (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    ambientPoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w) = ambientPoint 𝒜 𝒞 (ψ.comp φ) w :=
  ((ambientPoint_val ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w)).trans
      (projInclPt_val 𝒞 (mapDomain_comp_le 𝒜 ℬ 𝒞 φ ψ) w)).trans
    (ambientPoint_val 𝒜 𝒞 (ψ.comp φ) w).symm

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The image under the outer morphism of a point of the domain of definition of the composite
lies in the domain of definition of the inner homomorphism. This is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_mapDomain`. -/
public theorem basePoint_outerPt_mem (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w) ∈ mapDomain 𝒜 ℬ φ := by
  refine base_mem_of_mem_preimage (mapHom ℬ 𝒞 ψ) (mapDomain 𝒜 ℬ φ) _ ?_
  rw [mapHom_preimage_mapDomain 𝒜 ℬ 𝒞 φ ψ]
  refine mem_preimage_ι (mapDomain 𝒜 𝒞 (ψ.comp φ)) (outerPt 𝒜 ℬ 𝒞 φ ψ w) ?_
  rw [outerPt_val 𝒜 ℬ 𝒞 φ ψ w]
  exact w.2

/-- **The point of the domain of definition of the inner homomorphism through which the
composite factors at `w`.** -/
public def innerPt (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) : (mapDomain 𝒜 ℬ φ).toScheme :=
  ⟨basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w), basePoint_outerPt_mem 𝒜 ℬ 𝒞 φ ψ w⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `innerPt` is the image of `outerPt` under the outer morphism. -/
public theorem ambientPoint_innerPt (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    ambientPoint 𝒜 ℬ φ (innerPt 𝒜 ℬ 𝒞 φ ψ w) =
      basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w) :=
  (ambientPoint_val 𝒜 ℬ φ (innerPt 𝒜 ℬ 𝒞 φ ψ w)).trans
    (projMk_val ℬ _ (basePoint_outerPt_mem 𝒜 ℬ 𝒞 φ ψ w))

/-- **The homogeneous ideal at the image of a point under the composite is the `φ`-preimage of
the one at its image under the outer morphism.**

This is `Stacks.AlgebraicGeometry.ProjTwistCompare.basePoint_asHomogeneousIdeal` twice, together
with `HomogeneousIdeal.comap_comap`, and it is the hypothesis
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp` asks for in the composite situation. -/
public theorem basePoint_comp_asHomogeneousIdeal (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    (basePoint 𝒜 𝒞 (ψ.comp φ) w).asHomogeneousIdeal =
      (basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w)).asHomogeneousIdeal.comap φ := by
  rw [basePoint_asHomogeneousIdeal 𝒜 𝒞 (ψ.comp φ) w,
    basePoint_asHomogeneousIdeal ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w),
    ambientPoint_outerPt 𝒜 ℬ 𝒞 φ ψ w, HomogeneousIdeal.comap_comap φ ψ]

/-- **The two readings of the image point agree.** The image of `w` under the morphism induced by
the composite is the image under the inner morphism of the image under the outer one, as a point
of `Proj 𝒜`. -/
public theorem basePoint_innerPt (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    basePoint 𝒜 ℬ φ (innerPt 𝒜 ℬ 𝒞 φ ψ w) = basePoint 𝒜 𝒞 (ψ.comp φ) w := by
  refine ProjectiveSpectrum.ext ?_
  rw [basePoint_asHomogeneousIdeal 𝒜 ℬ φ (innerPt 𝒜 ℬ 𝒞 φ ψ w),
    ambientPoint_innerPt 𝒜 ℬ 𝒞 φ ψ w, ← basePoint_comp_asHomogeneousIdeal 𝒜 ℬ 𝒞 φ ψ w]

/-- **The comparison on fibres of a composite factors as the composite of the comparisons.**
This is the mathematical content of Tag 01MZ's assertion about the maps on all twists: the
underlying module of every twist is the ring itself, so the comparison on a fibre is
`Localization.localRingHom` and the composition law is
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp`.

The intermediate relevant homogeneous prime `y` is a **free argument**, constrained only by its
homogeneous ideal. That is what makes the statement transport-free: the only point of `Proj 𝒞`
it mentions is `ambientPoint 𝒜 𝒞 (ψ.comp φ) w`, so no identification of two readings of that
point has to be type-checked. The canonical choice of `y` is
`basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w)`, whose two hypotheses are
`basePoint_comp_asHomogeneousIdeal` and `basePoint_asHomogeneousIdeal` transported along
`ambientPoint_outerPt`. -/
public theorem twistFibreMap_eq_comp (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme)
    (y : ProjectiveSpectrum ℬ)
    (hxy : (basePoint 𝒜 𝒞 (ψ.comp φ) w).asHomogeneousIdeal = y.asHomogeneousIdeal.comap φ)
    (hyz : y.asHomogeneousIdeal =
      (ambientPoint 𝒜 𝒞 (ψ.comp φ) w).asHomogeneousIdeal.comap ψ) :
    twistFibreMap 𝒜 𝒞 (ψ.comp φ) w =
      (fibreMap ℬ 𝒞 ψ y (ambientPoint 𝒜 𝒞 (ψ.comp φ) w) hyz).comp
        (fibreMap 𝒜 ℬ φ (basePoint 𝒜 𝒞 (ψ.comp φ) w) y hxy) :=
  fibreMap_comp 𝒜 ℬ 𝒞 φ ψ _ _ _ hxy hyz
    (basePoint_asHomogeneousIdeal 𝒜 𝒞 (ψ.comp φ) w)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The hypothesis `twistFibreMap_eq_comp` asks for at the canonical intermediate prime. -/
public theorem basePoint_outerPt_asHomogeneousIdeal
    (w : (mapDomain 𝒜 𝒞 (ψ.comp φ)).toScheme) :
    (basePoint ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w)).asHomogeneousIdeal =
      (ambientPoint 𝒜 𝒞 (ψ.comp φ) w).asHomogeneousIdeal.comap ψ := by
  rw [basePoint_asHomogeneousIdeal ℬ 𝒞 ψ (outerPt 𝒜 ℬ 𝒞 φ ψ w),
    ambientPoint_outerPt 𝒜 ℬ 𝒞 φ ψ w]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The identity Tag 01MZ's twist assertion feeds to the last of its nine factors.** The
canonical isomorphism from `V = r_ψ⁻¹(U(φ))` to the domain of definition of the composite,
followed by the inclusion of that domain, is the inclusion of `V` followed by the inclusion of
the domain of definition of `ψ`. -/
public theorem compIso_hom_comp_ι :
    (((mapDomain ℬ 𝒞 ψ).ι.isoImage (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ)) ≪≫
        (AlgebraicGeometry.Proj 𝒞).isoOfEq (mapDomain_comp 𝒜 ℬ 𝒞 φ ψ).symm).hom ≫
        (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι =
      (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι ≫ (mapDomain ℬ 𝒞 ψ).ι := by
  rw [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]

end Comp

end Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality

end
