module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.FlatBaseChangeSections

/-!
# The Čech differentials agree with the Amitsur differentials, and the fpqc consequence

Let `F` be a sheaf of modules on the big `τ`-site over `S` and let `Spec A' → Spec A` be a flat
surjective morphism of affines of the site. [Stacks, Tag 06VL] identifies the terms of the
extended Čech complex
`0 → F(Spec A) → F(Spec A') → F(Spec (A' ⊗_A A')) → ⋯`
with the terms of the extended Amitsur complex of `A → A'` with coefficients `F(Spec A)`, using
flat base change, and then concludes exactness from [Stacks, Tag 023M]. The termwise step and
the exactness step are carried out in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/FlatBaseChangeSections.lean`.

**This module supplies the step between them**, which neither that file nor the source states:
the termwise identifications are compatible with the transition maps, so the two complexes have
the same differentials and not merely the same terms. The source of [Stacks, Tag 03FJ], where
the same identification is made, says explicitly "we omit the verification that the maps of the
Čech complex agree with the maps in the complex `s((A/R)_• ⊗_R M)`";
`Stacks.CechSite.conerveSectionsMap_naturality` carries that verification out for a presheaf on
a site, and the present module carries it out for the base-change maps of a module-valued
functor, which is the form Tag 06VL uses.

The compatibility is unconditional: it needs neither flatness nor adequacy. Those enter only to
make the comparison maps bijective, which is [Stacks, Tag 06UW] in the form
`Stacks.Adequate.bijective_affineSectionBaseChangeMap_base`. So the content here is exactly the
omitted verification and nothing else.

## Main definitions

* `AdequateFunctor.transitionLinearMap` is a transition map `ι(C) ⟶ ι(E)` of the algebra domain,
  read as a linear map over the base algebra `ι(B)` along a chosen map `B ⟶ C`. It is the map
  inducing the differentials of the Amitsur complex.
* `Stacks.Adequate.fpqcPrecoverageOn` and `Stacks.Adequate.fppfPrecoverageOn` are the fpqc and
  fppf covering families of a chosen big site: the families of the site whose images are fpqc,
  respectively fppf, covering families of schemes.

## Main results

* `AdequateFunctor.moduleValuedFunctorBaseChangeMap_naturality` — **the omitted verification.**
  For morphisms `u : B ⟶ C` and `v : C ⟶ E` of the algebra domain, the square

  ```
      ι(C) ⊗_{ι(B)} F(B)  --base change along u-->  F(C)
            |                                        |
       ι(v) ⊗ id                                   F(v)
            v                                        v
      ι(E) ⊗_{ι(B)} F(B)  --base change along u≫v--> F(E)
  ```

  commutes. Taking `B` to be the base algebra and `v` to run over the coface maps of the Čech
  conerve, this says that the identifications of the terms of the extended Čech complex with the
  terms of the extended Amitsur complex carry one coface map to the other, hence one alternating
  sum to the other.
* `Stacks.Adequate.affineSectionBaseChangeMap_naturality` is the same statement for the
  affine-section functor of a sheaf of modules on a big site, which is the setting of Tag 06VL.
* `Stacks.Adequate.isSheaf_fppf_of_isSheaf_fpqc` — the second sheaf conclusion of Tag 06VL
  follows from the first: a presheaf on the big site satisfying the sheaf condition for fpqc
  covering families satisfies it for fppf covering families, because an fppf covering family is
  an fpqc covering family.

## Implementation notes

`AdequateFunctor.moduleValuedFunctorBaseChangeMap_naturality` is stated for an arbitrary
`ι : D ⥤ CommAlgCat A`, not only for the site algebras of Tag 06VL, because the base-change map
`AdequateFunctor.moduleValuedFunctorBaseChangeMap` is defined at that generality and the proof
uses nothing else: on a pure tensor both sides are the scalar multiple of a transition value,
and the scalars match by `PresheafOfModules.map_smul` together with functoriality of `F`.

**How this relates to the general-site Čech/Amitsur machinery, which does exist.** The claim to
make for `AdequateFunctor.moduleValuedFunctorBaseChangeMap_naturality` is not that no Čech/Amitsur
differential comparison was in the library — two were. It is that both of them *consume* a
statement of the shape proved here rather than supplying it.
`PresheafOfModules.cechDiff₀_eq_amitsurDiff₀`, in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/BigSiteColimits/CechAmitsur.lean`, is an
assembler: it takes as hypotheses one equation per projection — restriction along that projection
of a section is base change of the sections along the corresponding ring map of the double
self-product — and assembles their difference into `Module.Descent.amitsurDiff₀`. Its own
docstring says so: "A consumer does not have the Čech differential identified with
`Module.Descent.amitsurDiff₀`; it has one description per projection". Those per-projection
equations are what the naturality square below proves, unconditionally, for the base-change maps
of a module-valued functor on an algebra domain, the coface maps of the Čech conerve being its
`v`. So the two compose and neither subsumes the other. Likewise
`Stacks.CechSite.conerveSectionsMap_naturality`, in
`StacksFrontier/AlgebraicGeometry/Descent/Module/CechAmitsurComparison.lean`, is the comparison for
a
presheaf on a site, already cited for that role in the implementation notes of
`FlatBaseChangeSections.lean`; it is not stated for `AdequateFunctor.ModuleValuedFunctorOn` and
does not give the base-change form.

The *direction* of the general-site results matters to anyone arriving here for a Čech-exactness
statement: `PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` and
`PresheafOfModules.surjective_toCechCocycleZero` run from degree-zero exactness of the Amitsur
complex *to* the sheaf condition for a one-element covering. The converse — an element-level Čech
exactness statement derived *from* the sheaf condition — is in neither that file nor this one.

The two source and target tensor products are formed over *different* `Algebra (ι B) (-)`
instances — the ones induced by `u` and by `u ≫ v` — so the vertical map of the square is not
`LinearMap.rTensor` of an ambient algebra map. `AdequateFunctor.transitionLinearMap` records
that `ι(v)` is nevertheless `ι(B)`-linear for those two instances, which is exactly the
statement that `v` is a morphism *under* `B`.

**What is not done here.** The fpqc sheaf conclusion itself is not proved. Reducing the fpqc
sheaf condition to the Zariski one together with the sheaf condition for a single faithfully
flat morphism of affines is [Stacks, Tag 03O1], available as
`Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton`, but only for presheaves
on *all* schemes over `S`; a module on a chosen big site is defined only on the schemes below
the site's cardinal cutoff. That missing form, and not the exactness, is what the final paragraph
of Tag 06VL — for which the source itself says "details omitted" — still needs. It is supplied,
for a presheaf of the site which extends to the schemes over `S`, by
`Stacks.Adequate.isSheaf_fpqc_of_exists_extension` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/BigSiteFpqcSheafCriterion.lean`, whose
implementation notes record what is still missing without that extension hypothesis and why.
Accordingly no `@[stacks 06VL]` attribute is attached in this module.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AdequateFunctor Opposite
open scoped TensorProduct

universe w v u v₁ u₁ m

namespace AdequateFunctor

variable {A : Type u} [CommRing A] {D : Type u₁} [Category.{v₁} D]
  (ι : D ⥤ CommAlgCat.{max u v} A)

/-- A transition map `ι(C) ⟶ ι(E)` of the algebra domain, read as a linear map over the base
algebra `ι(B)` along a chosen map `u : B ⟶ C`. The two sides carry the `ι(B)`-algebra structures
induced by `u` and by `u ≫ v`, and `ι(v)` is linear for them because `v` is a morphism under
`B`. -/
public def transitionLinearMap {B C E : D} (u : B ⟶ C) (v : C ⟶ E) :
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
    letI : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
    ι.obj C →ₗ[ι.obj B] ι.obj E := by
  letI : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
  letI : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
  exact
  { toFun := fun c => (ι.map v).hom c
    map_add' := fun c d => map_add (ι.map v).hom c d
    map_smul' := fun b c => by
      change (ι.map v).hom ((ι.map u).hom b * c) =
        (ι.map (u ≫ v)).hom b * (ι.map v).hom c
      rw [map_mul]
      refine congrArg (· * (ι.map v).hom c) ?_
      change ((ι.map u) ≫ (ι.map v)).hom b = (ι.map (u ≫ v)).hom b
      rw [← ι.map_comp] }

/-- The linear map `transitionLinearMap ι u v` sends `c` to `ι(v)(c)`. -/
@[simp]
public theorem transitionLinearMap_apply {B C E : D} (u : B ⟶ C) (v : C ⟶ E) (c : ι.obj C) :
    transitionLinearMap ι u v c = (ι.map v).hom c := rfl

/-- The base-change comparison maps are compatible with the transition maps, on a pure tensor.
Both sides are `ι(v)(c)` times the value of `F` on the composite `u ≫ v`. -/
public theorem moduleValuedFunctorBaseChangeMap_map_tmul
    (F : ModuleValuedFunctorOn.{w} ι) {B C E : D} (u : B ⟶ C) (v : C ⟶ E)
    (c : ι.obj C) (x : F.obj (op (op B))) :
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
    letI : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
    F.map v.op.op (moduleValuedFunctorBaseChangeMap ι F u (c ⊗ₜ[ι.obj B] x)) =
      moduleValuedFunctorBaseChangeMap ι F (u ≫ v) ((ι.map v).hom c ⊗ₜ[ι.obj B] x) := by
  let : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
  let : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
  rw [moduleValuedFunctorBaseChangeMap_tmul, moduleValuedFunctorBaseChangeMap_tmul,
    show ((u ≫ v).op.op) = u.op.op ≫ v.op.op from rfl, F.map_comp_apply]
  exact F.map_smul v.op.op c _

/-- **The base-change comparison maps commute with the transition maps.**

This is the verification that the source of [Stacks, Tag 03FJ] omits, in the form [Stacks, Tag
06VL] uses: with `B` the base algebra and `v` running over the coface maps of the Čech conerve,
the identifications `ι(C) ⊗_{ι(B)} F(B) ≅ F(C)` of the terms of the extended Čech complex with
the terms of the extended Amitsur complex carry each coface map of one complex to the coface map
of the other, hence each alternating sum to the other. No flatness and no adequacy is used; they
are needed only to make the comparison maps bijective, which is [Stacks, Tag 06UW]. -/
public theorem moduleValuedFunctorBaseChangeMap_naturality
    (F : ModuleValuedFunctorOn.{w} ι) {B C E : D} (u : B ⟶ C) (v : C ⟶ E) :
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
    letI : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
    ∀ z : (ι.obj C) ⊗[ι.obj B] F.obj (op (op B)),
      F.map v.op.op (moduleValuedFunctorBaseChangeMap ι F u z) =
        moduleValuedFunctorBaseChangeMap ι F (u ≫ v)
          (LinearMap.rTensor (F.obj (op (op B))) (transitionLinearMap ι u v) z) := by
  let : Algebra (ι.obj B) (ι.obj C) := (ι.map u).hom.toRingHom.toAlgebra
  let : Algebra (ι.obj B) (ι.obj E) := (ι.map (u ≫ v)).hom.toRingHom.toAlgebra
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c x => exact moduleValuedFunctorBaseChangeMap_map_tmul ι F u v c x
  | add z w hz hw =>
      rw [map_add, map_add, map_add, map_add, hz, hw]
      rfl

end AdequateFunctor

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The differential agreement for the affine sections of a sheaf of modules -/

/-- The structure morphism out of the base algebra is the only morphism out of it: composing it
with any morphism of the site algebras gives the structure morphism of the target. -/
public theorem baseAlgebraInSiteHom_comp (B : BigSite τ S) (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A))
    {C E : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)} (v : C ⟶ E) :
    baseAlgebraInSiteHom B A hA C ≫ v = baseAlgebraInSiteHom B A hA E :=
  baseAlgebraHom_comp (schemeSizeBelow B.cutoff) hA v

/-- **The flat base change identifications of Tag 06VL commute with the transition maps.**

For a sheaf of modules `F` on a big `τ`-site over `S` and an affine `Spec A` of the site, the
canonical maps `C ⊗_A F(Spec A) → F(Spec C)` of
`Stacks.Adequate.bijective_affineSectionBaseChangeMap_base` are compatible with every morphism
`v : C ⟶ E` of the site algebras. Applied to the coface maps of the Čech conerve of `A → A'`
this is the agreement of the differentials of the extended Čech complex of `Spec A' → Spec A`
with those of the extended Amitsur complex of `A → A'`, the step [Stacks, Tag 06VL] passes over
in silence. It holds for every `F` and every `v`: no adequacy, no flatness, no surjectivity. -/
public theorem affineSectionBaseChangeMap_naturality (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A))
    {C E : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)} (v : C ⟶ E) :
    letI ic := AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)
    letI u := baseAlgebraInSiteHom B A hA C
    letI : Algebra (ic.obj (baseAlgebraInSite B A hA)) (ic.obj C) :=
      (ic.map u).hom.toRingHom.toAlgebra
    letI : Algebra (ic.obj (baseAlgebraInSite B A hA)) (ic.obj E) :=
      (ic.map (u ≫ v)).hom.toRingHom.toAlgebra
    ∀ z : (ic.obj C) ⊗[ic.obj (baseAlgebraInSite B A hA)]
        (affineSectionFunctor B F A f).obj (op (op (baseAlgebraInSite B A hA))),
      (affineSectionFunctor B F A f).map v.op.op
          (AdequateFunctor.moduleValuedFunctorBaseChangeMap ic
            (affineSectionFunctor B F A f) u z) =
        AdequateFunctor.moduleValuedFunctorBaseChangeMap ic
          (affineSectionFunctor B F A f) (u ≫ v)
          (LinearMap.rTensor
            ((affineSectionFunctor B F A f).obj (op (op (baseAlgebraInSite B A hA))))
            (AdequateFunctor.transitionLinearMap ic u v) z) :=
  AdequateFunctor.moduleValuedFunctorBaseChangeMap_naturality _ _ _ _

/-! ### The fpqc and fppf covering families of a chosen big site -/

/-- The fpqc covering families of a chosen big site: the families of the site whose images are
fpqc covering families of schemes. This is the sense in which [Stacks, Tag 06VL] asserts that an
adequate module "satisfies the sheaf condition for fpqc coverings". -/
public abbrev fpqcPrecoverageOn (B : BigSite τ S) : Precoverage B.category :=
  Scheme.fpqcPrecoverage.{u}.comap (B.toOver ⋙ Over.forget S)

/-- The fppf covering families of a chosen big site. -/
public abbrev fppfPrecoverageOn (B : BigSite τ S) : Precoverage B.category :=
  Scheme.fppfPrecoverage.{u}.comap (B.toOver ⋙ Over.forget S)

/-- An fppf covering family of the site is an fpqc covering family of the site, because an fppf
covering family of schemes is an fpqc covering family of schemes. -/
public theorem fppfPrecoverageOn_le_fpqcPrecoverageOn (B : BigSite τ S) :
    fppfPrecoverageOn B ≤ fpqcPrecoverageOn B := fun _ _ hR =>
  Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hR

/-- **A flat surjective morphism between affines of the site is an fpqc covering of the site.**
This is the covering for which [Stacks, Tag 06VL] proves the extended Čech complex exact, so it
is the one whose sheaf condition the tag's first sheaf conclusion rests on. Quasi-compactness,
which the fpqc condition also demands, is automatic: a morphism of affine schemes is affine. -/
public theorem sieve_generate_singleton_mem_fpqc (B : BigSite τ S) {X T : B.category}
    (g : X ⟶ T) (hX : IsAffine ((B.toOver.obj X).left)) (hT : IsAffine ((B.toOver.obj T).left))
    (hflat : Flat ((B.toOver.map g).left)) (hsurj : Surjective ((B.toOver.map g).left)) :
    Sieve.generate (Presieve.singleton g) ∈ (fpqcPrecoverageOn B).toGrothendieck T := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
  have hX' : IsAffine ((B.toOver ⋙ Over.forget S).obj X) := hX
  have hT' : IsAffine ((B.toOver ⋙ Over.forget S).obj T) := hT
  have hflat' : Flat ((B.toOver ⋙ Over.forget S).map g) := hflat
  have hsurj' : Surjective ((B.toOver ⋙ Over.forget S).map g) := hsurj
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-- **The fppf sheaf conclusion of [Stacks, Tag 06VL] follows from the fpqc one.** A presheaf on
a chosen big site which satisfies the sheaf condition for the fpqc covering families of the site
satisfies it for the fppf covering families, since the latter are among the former. The source
states the two conclusions side by side — "satisfies the sheaf condition for fpqc coverings, and
is a sheaf of `𝒪`-modules on `(Sch/S)_fppf`" — and this is the implication between them. -/
public theorem isSheaf_fppf_of_isSheaf_fpqc (B : BigSite τ S) {Z : Type*} [Category Z]
    (P : B.categoryᵒᵖ ⥤ Z)
    (h : Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck P :=
  h.of_le (Precoverage.toGrothendieck_mono (fppfPrecoverageOn_le_fpqcPrecoverageOn B))

end Stacks.Adequate

end
