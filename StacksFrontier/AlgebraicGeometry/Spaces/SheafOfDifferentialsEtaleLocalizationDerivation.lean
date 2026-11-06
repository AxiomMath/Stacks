module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization

/-!
# The identification of [Stacks Project, Tag 04CU] carries one universal differential to the other

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B` and let `a ≫ f = ψ ≫ b` be a commuting square with `a : U ⟶ X` and `b : V ⟶ Y` étale.
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` is [Stacks Project, Tag 04CU]:

`a^*Ω_{X/Y} ≅ Ω_{U/V}`.

This file proves that it is the **canonical** comparison and not merely some isomorphism: read as
a `Y`-derivation of `𝒪_U` by the four bijections of
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv`, it returns the universal differential
`d_{U/V}(x)` of every local section `x` of `𝒪_U`.

Each of the two geometric steps the isomorphism is composed of already had this property on its
own — `AlgebraicGeometry.Space.universalDerivation_etaleSourceLocalizationHom` for the
étale-source step of [Stacks Project, Tag 03LP], [Stacks Project, Tag 03LQ] and
[Stacks Project, Tag 04BO], and `AlgebraicGeometry.Space.postcomp_sharpIsoInv` for the
étale-base step of [Stacks Project, Tag 03G8] and [Stacks Project, Tag 03LV].  What was missing
was their composite, which is what a consumer reading a section of a sheaf of differentials on an
étale scheme chart actually needs.

## Main results

* `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso_eq`,
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso_hom` and
  `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso_inv`: the three equation lemmas the
  composite is assembled through.  Each is `rfl`, and stating them separately is what makes the
  assembly affordable — see the implementation notes.
* `AlgebraicGeometry.Space.postcomp_sharpIsoInv_d`: the étale-base step on a local section.
* `AlgebraicGeometry.Space.derivationEtalePullbackEquiv_localizationComposite_d`: the composite
  with its three factors written out and the factorization of the square an equation at a
  *variable* composite, which is what lets the middle `CategoryTheory.eqToIso` be removed by
  `subst`.
* `AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsEtaleLocalizationIso`:
  **[Stacks Project, Tag 04CU] on local sections** — the identification, read as a derivation,
  is the universal differential of `Ω_{U/V}`.

## Implementation notes

**Why the three equation lemmas are separate declarations, and not `have`s.**  Assembling the
composite inside one declaration exhausts the 200 000-heartbeat *kernel* budget — not the
elaborator's, which succeeds in 50 to 90 seconds.  Each of the following five routes fails
the same way: `rfl` under `.hom`, `rfl` at the level of the isomorphisms followed by
`CategoryTheory.Iso.trans_hom`, `rw` with either, `simp only` unfolding the definition, and
`congrArg` at isomorphism level with the context fully written out.

The cost is **not** the delta-reduction of
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`: that equation on its own,
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso_eq`, checks in a fifth of a
second.  Neither is it the statement, which checks as a reflexive instance of itself.  The cost
is **projecting `.hom` and `.inv` out of the two isomorphisms built as structure literals**:
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` and
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` each carry
`CategoryTheory.Iso.hom_inv_id` and `CategoryTheory.Iso.inv_hom_id` proof fields which are large
derivation computations, and whnf of the structure instance drags those in every time the
projection is taken.  Naming each projection in its own declaration makes the kernel do that once
and lets every later step cite a constant: the whole chain then checks in 2.2 seconds.

**This refines the development's standing rule** that a transport should be identified at the
level it was stated.  That rule is about *which level* the `rfl` is taken at; here the `rfl` is
affordable at every level, and what has to be factored out is the *projection out of a structure
literal whose proof fields are expensive*.  The symptom is distinctive: a kernel timeout with no
elaboration error, on a declaration whose statement and whose definitional unfolding are each
cheap in isolation.

**Why the factorization is generalized to a variable.**  The middle factor of the composite is
`CategoryTheory.eqToIso` at `hcomm : a ≫ f = ψ ≫ b`, and neither side of that equation is a
variable, so `subst` cannot fire on it.  Taking the target as a variable `c` with
`hcomm : a ≫ f = c` makes it substitutable, after which the `eqToIso` is the identity and
`CategoryTheory.Category.id_comp` removes it;
`AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsEtaleLocalizationIso` then
instantiates at `c := ψ ≫ b`.  Stating the composite lemma over a derivation rather than over a
local section is not possible: the two sides would be derivations over the two different base
sheaves `(a ≫ f)^{-1}𝒪_Y` and `c^{-1}𝒪_Y`, so the equation is ill-typed before the `subst`,
whereas at a local section the base does not appear in the type.

No `@[stacks]` attribute is claimed: [Stacks Project, Tag 04CU] is registered at
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` itself, and what is added here
is that the registered isomorphism is the canonical one.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y U V : AlgebraicSpaces B S hS}

/-! ### The three equation lemmas -/

/-- The forward map of the étale-source localization of [Stacks Project, Tag 04CU] is
`AlgebraicGeometry.Space.etaleSourceLocalizationHom`, named so that no later step has to project
it out of the isomorphism's structure literal. -/
theorem sheafOfDifferentialsEtaleSourceLocalizationIso_hom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).hom =
      etaleSourceLocalizationHom B S hS a ha f :=
  rfl

/-- The backward map of the étale-base step of [Stacks Project, Tag 04CU] is
`AlgebraicGeometry.Space.sharpIsoInv`, named for the same reason. -/
theorem sheafOfDifferentialsIsoOfSharpIso_inv (p : U ⟶ Y) (q : U ⟶ V)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    (sheafOfDifferentialsIsoOfSharpIso B S hS p q e he).inv = sharpIsoInv B S hS p q e he :=
  rfl

/-- The identification of [Stacks Project, Tag 04CU] **is** its defining composite of the
étale-source localization, the transport along the square and the étale-base step. -/
theorem sheafOfDifferentialsEtaleLocalizationIso_eq (f : X ⟶ Y) (a : U ⟶ X) (ψ : U ⟶ V)
    (b : V ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = ψ ≫ b) :
    sheafOfDifferentialsEtaleLocalizationIso B S hS f a ψ b ha hb hcomm =
      sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f ≪≫
        eqToIso (congrArg (fun g : U ⟶ Y => sheafOfDifferentials B S hS g) hcomm) ≪≫
        (sheafOfDifferentialsIsoOfSharpIso B S hS ψ (ψ ≫ b)
          (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb)
          (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage
            B S hS ψ b hb)).symm :=
  rfl

/-! ### The étale-base step on a local section -/

/-- **The étale-base step of [Stacks Project, Tag 04CU] carries one universal differential to the
other, on a local section.**  This is the defining property
`AlgebraicGeometry.Space.postcomp_sharpIsoInv` read at a section, the change of base sheaf being
invisible to `PresheafOfModules.Derivation'.precompBase`. -/
theorem postcomp_sharpIsoInv_d (p : U ⟶ Y) (q : U ⟶ V)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q)
    {W : (SmallEtale B S hS U.1)ᵒᵖ} (x : (structureRingSheaf B S hS U).obj.obj W) :
    ((universalDerivation B S hS q).postcomp (sharpIsoInv B S hS p q e he).val).d x =
      (universalDerivation B S hS p).d x :=
  PresheafOfModulesOfCommRing.Derivation.congr_d (postcomp_sharpIsoInv B S hS p q e he) x

/-! ### The composite -/

/-- **The composite of the three factors of [Stacks Project, Tag 04CU], read as a derivation on a
local section.**  The factorization of the square is taken as an equation at a *variable*
composite `c`, which is what makes the middle `CategoryTheory.eqToIso` removable by `subst`;
the module documentation says why no formulation over a derivation is available. -/
theorem derivationEtalePullbackEquiv_localizationComposite_d (f : X ⟶ Y) (a : U ⟶ X) (ψ : U ⟶ V)
    (ha : IsEtale B S hS a.hom) {c : U ⟶ Y} (hcomm : a ≫ f = c)
    (e : inverseImageStructureSheaf B S hS c ≅ inverseImageStructureSheaf B S hS ψ)
    (he : e.hom ≫ structureSharpInverseImage B S hS ψ =
      structureSharpInverseImage B S hS c)
    {W : (SmallEtale B S hS U.1)ᵒᵖ} (x : (structureRingSheaf B S hS U).obj.obj W) :
    (derivationEtalePullbackEquiv B S hS a ha f (sheafOfDifferentials B S hS ψ)
        (etaleSourceLocalizationHom B S hS a ha f ≫
          ((eqToIso (congrArg (fun g : U ⟶ Y => sheafOfDifferentials B S hS g) hcomm)).hom ≫
            sharpIsoInv B S hS ψ c e he))).d x =
      (universalDerivation B S hS ψ).d x := by
  subst hcomm
  have hid : etaleSourceLocalizationHom B S hS a ha f ≫
        ((eqToIso (congrArg (fun g : U ⟶ Y => sheafOfDifferentials B S hS g)
            (rfl : a ≫ f = a ≫ f))).hom ≫ sharpIsoInv B S hS ψ (a ≫ f) e he) =
      etaleSourceLocalizationHom B S hS a ha f ≫ sharpIsoInv B S hS ψ (a ≫ f) e he := by
    simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  rw [hid, derivationEtalePullbackEquiv_comp,
    derivationEtalePullbackEquiv_etaleSourceLocalizationHom]
  exact postcomp_sharpIsoInv_d B S hS ψ (a ≫ f) e he x

/-- **[Stacks Project, Tag 04CU] on local sections.**  Reading the identification
`a^*Ω_{X/Y} ≅ Ω_{U/V}` of a square of étale charts as a `Y`-derivation of `𝒪_U`, by the four
bijections of `AlgebraicGeometry.Space.derivationEtalePullbackEquiv`, returns the universal
differential `d_{U/V}(x)` of every local section `x` of `𝒪_U`.  So the identification is the
canonical comparison and not merely some isomorphism.

This is the composite form of
`AlgebraicGeometry.Space.universalDerivation_etaleSourceLocalizationHom` and
`AlgebraicGeometry.Space.postcomp_sharpIsoInv`, which are the same statement for the two
geometric steps separately. -/
theorem universalDerivation_sheafOfDifferentialsEtaleLocalizationIso (f : X ⟶ Y) (a : U ⟶ X)
    (ψ : U ⟶ V) (b : V ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = ψ ≫ b)
    {W : (SmallEtale B S hS U.1)ᵒᵖ} (x : (structureRingSheaf B S hS U).obj.obj W) :
    (derivationEtalePullbackEquiv B S hS a ha f (sheafOfDifferentials B S hS ψ)
        (sheafOfDifferentialsEtaleLocalizationIso B S hS f a ψ b ha hb hcomm).hom).d x =
      (universalDerivation B S hS ψ).d x := by
  rw [sheafOfDifferentialsEtaleLocalizationIso_eq B S hS f a ψ b ha hb hcomm, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, sheafOfDifferentialsEtaleSourceLocalizationIso_hom B S hS a ha f,
    sheafOfDifferentialsIsoOfSharpIso_inv B S hS ψ (ψ ≫ b)]
  exact derivationEtalePullbackEquiv_localizationComposite_d B S hS f a ψ ha hcomm
    (etaleBaseInverseImageStructureSheafIso B S hS ψ b hb)
    (etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS ψ b hb) x

end AlgebraicGeometry.Space

end
