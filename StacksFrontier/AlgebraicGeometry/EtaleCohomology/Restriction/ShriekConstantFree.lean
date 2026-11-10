module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.CategoryTheory.Sites.Density
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two spellings of the extension by zero of a constant module sheaf agree

The sheaf `j_{U!}\underline{\Lambda}_U` that Stacks 095N presents a constructible module sheaf by
has two realizations in this library, which are identified here.

* `AlgebraicGeometry.moduleShriekConstant` builds it as the sheaf pullback, along composition with
  `U ⟶ X`, of the constant sheaf with value the free rank-one module. This is the generator of
  `AlgebraicGeometry.HasFiniteShriekPresentation`.
* `CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.free R)` applied to the sheafified
  representable `h_U^#` builds it as the free module sheaf on `h_U^#`. This is the generator in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves`.

Both are values of a composite left adjoint, and the identification is made here by comparing the
functors the two corepresent. Each corepresents sections over `U` followed by the forgetful
functor: for the free module sheaf by the adjunction `ModuleCat.free R ⊣ forget` transported to
sheaves (`CategoryTheory.Sheaf.adjunction`) followed by Yoneda's lemma for sheaves of sets
(`CategoryTheory.Sheaf.sectionEquiv`); for the sheaf pullback of the constant sheaf by the
composite of the constant-sheaf adjunction with the sheaf pullback adjunction, followed by
`ModuleCat.coyonedaULiftSelfIso`, which says maps out of the free rank-one module are its
elements. Since `CategoryTheory.coyoneda` is fully faithful, the two objects are isomorphic. Only
the first of the two corepresentation statements mentions `ModuleCat.free`, so only it ties the
ring universe to the module universe.

Nothing here mentions schemes except the last two results, which specialize the comparison to the
small étale site; the general statements hold for an arbitrary continuous functor of sites out of a
site with a terminal object.

## Main results

* `CategoryTheory.Sheaf.freeSectionEquiv` — **maps out of the free module sheaf on a sheafified
  representable are sections**: a morphism from it into `F` is a section of `F` over `U`.
* `CategoryTheory.Sheaf.coyonedaComposeAndSheafifyFreeIso` and
  `CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso` — the two corepresentation
  statements, as isomorphisms of corepresented functors.
* `CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree` — **the two spellings
  agree**: the sheaf pullback of the constant sheaf at the free rank-one module is the free module
  sheaf on the sheafified representable at the image of the terminal object.
* `CategoryTheory.Sheaf.exists_sheafPullbackConstantSheafIsoComposeAndSheafifyFree_bot` — the
  hypotheses of that statement are satisfiable.
* `CategoryTheory.Sheaf.hom_ext_of_coyonedaSections` and
  `CategoryTheory.Sheaf.epi_desc_of_coyonedaSections` — **a family of sheaves corepresenting
  sections generates**: every sheaf of modules is a quotient of the direct sum of them over all
  pairs of an object and a section over it. This is the generation step of Stacks 093B part (2) and
  of the proof of Stacks 093C, in the category of `ModuleCat R`-valued sheaves.
* `AlgebraicGeometry.moduleShriekConstantIsoFree` — the comparison on the small étale site, so that
  the generator of `AlgebraicGeometry.HasFiniteShriekPresentation` is the free module sheaf on a
  sheafified representable.
* `AlgebraicGeometry.moduleShriekConstantCoyonedaIso` and
  `AlgebraicGeometry.moduleShriekConstantSectionEquiv` — **maps out of
  `AlgebraicGeometry.moduleShriekConstant` at `U` are sections over `U`**, which is what produces
  the morphisms in a presentation. These do not go through `ModuleCat.free` and so leave the ring
  universe free.
* `AlgebraicGeometry.epi_desc_moduleShriekConstant` — and hence **every sheaf of modules on the
  small étale site is a quotient of a direct sum of extensions by zero of constant free rank-one
  module sheaves**, which is the generation step of the proof of Stacks 095N.

## Implementation notes

The comparison of corepresented functors is stated with module coefficients rather than for an
arbitrary coefficient category, and that is forced. The hom sets of `Sheaf J A` for a site
`C : Type u` live in `Type (max u vA)`, while those of `A` live in `Type vA`, so the two
corepresented functors land in the same universe only when `vA` absorbs `u`. At the module
coefficient universe `max u v w` used here it does, and at the universe `max u v` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves` it does too,
that universe being already forced there by the sheaves-of-sets statement being transported.

Where `ModuleCat.free` appears the ring universe is forced to equal the module universe, the
functor `Type r ⥤ ModuleCat.{r} R` carrying the ring and the module in one universe; that is the
case for `CategoryTheory.Sheaf.freeSectionEquiv`,
`CategoryTheory.Sheaf.coyonedaComposeAndSheafifyFreeIso`,
`CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree` and, on the small
étale site, for `AlgebraicGeometry.moduleShriekConstantIsoFree`. On the small étale site of
`X : B.Scheme` for `B : AlgebraicGeometry.BigEtaleSite.{u}` the objects form a `Type (u + 1)`
with `Category.{u}`, so there the ring is in `Type (u + 1)`, exactly as
`AlgebraicGeometry.isFinitelyPresentable_moduleShriekConstant` is.

The statements which avoid `ModuleCat.free` leave the ring universe free:
`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso`, which uses only the constant-sheaf
and sheaf-pullback adjunctions, and hence `AlgebraicGeometry.moduleShriekConstantCoyonedaIso` and
`AlgebraicGeometry.moduleShriekConstantSectionEquiv`, which compose it with
`ModuleCat.coyonedaULiftSelfIso`. That is what makes the generation step of Stacks 093B part (2)
available for a Noetherian ring in a universe of its own, which is the universe at which the
bounded above resolution of Stacks 0960 is stated.

The image of the terminal object under composition with `U ⟶ X` is isomorphic to `U` rather than
equal to it, so the étale comparison composes the general one with the image of
`AlgebraicGeometry.smallEtalePostcomposeFinalIso` under the two functors.

The generation statements are stated for an arbitrary family `P : C → Sheaf J (ModuleCat R)`
corepresenting sections rather than for either spelling, since both spellings satisfy the
hypothesis and the proof uses nothing else; they need no sheafification hypothesis at all. Both
`CategoryTheory.Sheaf.coyonedaComposeAndSheafifyFreeIso` and
`AlgebraicGeometry.moduleShriekConstantCoyonedaIso` inhabit that hypothesis, so it is exhibited
rather than assumed.

The direct sum in `AlgebraicGeometry.epi_desc_moduleShriekConstant` is taken with respect to a
`HasColimit` instance supplied by the caller, as the finite direct sums of
`AlgebraicGeometry.HasFiniteShriekPresentation` are, so that the two agree. It is satisfiable: at
`CategoryTheory.Sheaf.instHasColimitsOfShape`'s raised priority — the two coproduct instances are
given the priority they have in `AlgebraicGeometry.HasFiniteShriekPresentation`'s own file — it is
found, where at the default priority instance search exhausts its heartbeats.

The generation statements are the unrestricted form of Stacks 093B part (2): the index set is every
pair of an object and a section, where the source takes the objects from a distinguished covering
subcategory. Stacks 095N is the production of a *finite* presentation by *affine* objects, of which
this is one step.

## References

* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v' u' v u r w

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

namespace CategoryTheory.Sheaf

variable {C' : Type u'} [Category.{v'} C'] {C : Type u} [Category.{v} C]

/-- **Maps out of the free module sheaf on a sheafified representable are sections.** A morphism
from the free module sheaf on `h_U^#` into `F` is the same thing as a section of `F` over `U`:
the adjunction `ModuleCat.free R ⊣ forget` transported to sheaves, followed by Yoneda's lemma for
sheaves of sets. -/
@[sga "4 I 7.13" "special case"]
public def freeSectionEquiv (J : GrothendieckTopology C) (R : Type max u v) [Ring R]
    [HasWeakSheafify J (ModuleCat.{max u v} R)] (U : C)
    (F : Sheaf J (ModuleCat.{max u v} R)) :
    ((composeAndSheafify J (ModuleCat.free R)).obj ((sheafifiedYoneda J).obj U) ⟶ F) ≃
      (forget (ModuleCat.{max u v} R)).obj (F.obj.obj (op U)) :=
  ((adjunction J (ModuleCat.adj R)).homEquiv _ F).trans (sectionEquiv J)

/-- **The free module sheaf on `h_U^#` corepresents sections over `U`.** The isomorphism of
corepresented functors underlying `CategoryTheory.Sheaf.freeSectionEquiv`. -/
public def coyonedaComposeAndSheafifyFreeIso (J : GrothendieckTopology C) (R : Type max u v)
    [Ring R] [HasWeakSheafify J (ModuleCat.{max u v} R)] (U : C) :
    coyoneda.obj (op ((composeAndSheafify J (ModuleCat.free R)).obj
        ((sheafifiedYoneda J).obj U))) ≅
      (sheafSections J (ModuleCat.{max u v} R)).obj (op U) ⋙ forget (ModuleCat.{max u v} R) :=
  NatIso.ofComponents (fun F => Equiv.toIso (freeSectionEquiv J R U F)) (by
    intro F G φ
    ext α
    change sectionEquiv J ((adjunction J (ModuleCat.adj R)).homEquiv _ _ (α ≫ φ)) = _
    rw [(adjunction J (ModuleCat.adj R)).homEquiv_naturality_right, sectionEquiv_comp]
    rfl)

/-- **The sheaf pullback of a constant sheaf corepresents maps out of its value.** For a
continuous functor `π` out of a site with terminal object `T`, morphisms from the sheaf pullback
along `π` of the constant sheaf at `M` into `F` are morphisms from `M` into the sections of `F`
over `π.obj T`: the constant-sheaf adjunction composed with the sheaf pullback adjunction. -/
public def coyonedaSheafPullbackConstantSheafIso (π : C' ⥤ C) (JC' : GrothendieckTopology C')
    (JC : GrothendieckTopology C) [π.IsContinuous JC' JC] (R : Type r) [Ring R]
    [HasWeakSheafify JC' (ModuleCat.{max u v w} R)] [HasWeakSheafify JC (ModuleCat.{max u v w} R)]
    [∀ (F : C'ᵒᵖ ⥤ ModuleCat.{max u v w} R), π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) (M : ModuleCat.{max u v w} R) :
    coyoneda.obj (op ((Functor.sheafPullbackConstruction.sheafPullback π
        (ModuleCat.{max u v w} R) JC' JC).obj
        ((constantSheaf JC' (ModuleCat.{max u v w} R)).obj M))) ≅
      (sheafSections JC (ModuleCat.{max u v w} R)).obj (op (π.obj T)) ⋙ coyoneda.obj (op M) :=
  have adj := (constantSheafAdj JC' (ModuleCat.{max u v w} R) hT).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous π
      (ModuleCat.{max u v w} R) JC' JC)
  NatIso.ofComponents (fun F => Equiv.toIso (adj.homEquiv M F)) (by
    intro F G φ
    ext α
    change adj.homEquiv M G (α ≫ φ) = _
    rw [adj.homEquiv_naturality_right]
    rfl)

/-- **The two spellings of `j_{U!}\underline{\Lambda}_U` agree.** For a continuous functor `π` out
of a site with terminal object `T`, the sheaf pullback along `π` of the constant sheaf at the free
rank-one module is the free module sheaf on the sheafified representable at `π.obj T`.

Both corepresent sections over `π.obj T` followed by the forgetful functor — the second by
`CategoryTheory.Sheaf.coyonedaComposeAndSheafifyFreeIso`, the first by
`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso` followed by
`ModuleCat.coyonedaULiftSelfIso` — and `CategoryTheory.coyoneda` is fully faithful. -/
public def sheafPullbackConstantSheafIsoComposeAndSheafifyFree (π : C' ⥤ C)
    (JC' : GrothendieckTopology C') (JC : GrothendieckTopology C) [π.IsContinuous JC' JC]
    (R : Type max u v) [Ring R]
    [HasWeakSheafify JC' (ModuleCat.{max u v} R)] [HasWeakSheafify JC (ModuleCat.{max u v} R)]
    [∀ (F : C'ᵒᵖ ⥤ ModuleCat.{max u v} R), π.op.HasLeftKanExtension F]
    {T : C'} (hT : IsTerminal T) :
    (Functor.sheafPullbackConstruction.sheafPullback π (ModuleCat.{max u v} R) JC' JC).obj
        ((constantSheaf JC' (ModuleCat.{max u v} R)).obj
          (ModuleCat.of R (ULift.{max u v} R))) ≅
      (composeAndSheafify JC (ModuleCat.free R)).obj ((sheafifiedYoneda JC).obj (π.obj T)) :=
  (Coyoneda.fullyFaithful.preimageIso
    ((coyonedaComposeAndSheafifyFreeIso JC R (π.obj T)).trans
      ((Functor.isoWhiskerLeft _
        (ModuleCat.coyonedaULiftSelfIso.{max u v, max u v} R).symm).trans
          (coyonedaSheafPullbackConstantSheafIso π JC' JC R hT
            (ModuleCat.of R (ULift.{max u v} R))).symm))).unop

/-- **The hypotheses above are satisfiable.** On the trivial topology, with `π` the identity
functor and `T` a terminal object of the site, module-valued presheaves admit weak sheafification
and the left Kan extensions exist, and the two sheaves compared are isomorphic. -/
public theorem exists_sheafPullbackConstantSheafIsoComposeAndSheafifyFree_bot
    {T : C} (hT : IsTerminal T) (R : Type max u v) [Ring R] :
    ∃ _h : HasWeakSheafify (⊥ : GrothendieckTopology C) (ModuleCat.{max u v} R),
      Nonempty
        ((Functor.sheafPullbackConstruction.sheafPullback (𝟭 C)
              (ModuleCat.{max u v} R) ⊥ ⊥).obj
            ((constantSheaf ⊥ (ModuleCat.{max u v} R)).obj
              (ModuleCat.of R (ULift.{max u v} R))) ≅
          (composeAndSheafify ⊥ (ModuleCat.free R)).obj ((sheafifiedYoneda ⊥).obj T)) :=
  ⟨hasWeakSheafify_moduleCat.{max u v, v, u} (⊥ : GrothendieckTopology C) R,
    ⟨sheafPullbackConstantSheafIsoComposeAndSheafifyFree (𝟭 C) ⊥ ⊥ R hT⟩⟩

/-- The pairs `(U, s)` of an object of the site and a section of `F` over it. -/
public abbrev Sections (J : GrothendieckTopology C) (R : Type max u v) [Ring R]
    (F : Sheaf J (ModuleCat.{max u v} R)) : Type max u v :=
  Σ U : C, (forget (ModuleCat.{max u v} R)).obj (F.obj.obj (op U))

omit [Category.{v'} C'] in
/-- **A family of sheaves corepresenting sections is jointly epimorphic.** If `P U` corepresents
sections over `U` for every object `U` of the site, then two morphisms out of `F` agreeing after
every morphism `P U ⟶ F` are equal.

This is the mechanism behind the generation statements of Stacks 093B and 093C: a section of `F`
over `U` is a morphism `P U ⟶ F`, so the morphisms out of the `P U` see every section of `F`, and
two morphisms out of a sheaf agreeing on every section are equal. -/
public theorem hom_ext_of_coyonedaSections (J : GrothendieckTopology C) (R : Type max u v) [Ring R]
    (P : C → Sheaf J (ModuleCat.{max u v} R))
    (ε : ∀ U, coyoneda.obj (op (P U)) ≅
      (sheafSections J (ModuleCat.{max u v} R)).obj (op U) ⋙ forget (ModuleCat.{max u v} R))
    {F G : Sheaf J (ModuleCat.{max u v} R)} (a b : F ⟶ G)
    (h : ∀ (U : C) (φ : P U ⟶ F), φ ≫ a = φ ≫ b) : a = b := by
  ext ⟨U⟩ s
  have key : ∀ c : F ⟶ G, (ε U).hom.app G ((ε U).inv.app F s ≫ c) = c.hom.app (op U) s := by
    intro c
    simpa using NatTrans.naturality_apply (ε U).hom c ((ε U).inv.app F s)
  rw [← key a, ← key b, h U]

omit [Category.{v'} C'] in
/-- **Every sheaf of modules is a quotient of a direct sum of sheaves corepresenting sections.**
The direct sum over all pairs `(U, s)` of an object of the site and a section of `F` over it, of
the corepresenting sheaves `P U`, maps onto `F` by the morphism that each section is.

This is the generation statement of Stacks 093B part (2) and the first step of the proof of Stacks
093C, in the category of `ModuleCat R`-valued sheaves. The index set is all of
`CategoryTheory.Sheaf.Sections`; cutting it down to the objects of a distinguished subcategory —
affine objects, for Stacks 095N — is a further step, and needs that those objects cover. -/
public theorem epi_desc_of_coyonedaSections (J : GrothendieckTopology C) (R : Type max u v)
    [Ring R] (P : C → Sheaf J (ModuleCat.{max u v} R))
    (ε : ∀ U, coyoneda.obj (op (P U)) ≅
      (sheafSections J (ModuleCat.{max u v} R)).obj (op U) ⋙ forget (ModuleCat.{max u v} R))
    (F : Sheaf J (ModuleCat.{max u v} R))
    [HasColimit (Discrete.functor fun p : Sections J R F => P p.1)] :
    Epi (Limits.Sigma.desc (fun p : Sections J R F => (ε p.1).inv.app F p.2)) := by
  refine ⟨fun {G} x y hxy => hom_ext_of_coyonedaSections J R P ε x y (fun U φ => ?_)⟩
  have hφ : Limits.Sigma.ι (fun p : Sections J R F => P p.1)
        (⟨U, (ε U).hom.app F φ⟩ : Sections J R F) ≫
      Limits.Sigma.desc (fun p : Sections J R F => (ε p.1).inv.app F p.2) = φ := by
    rw [Limits.Sigma.ι_comp_desc, Iso.hom_inv_id_app_apply]
  rw [← hφ, Category.assoc, Category.assoc, hxy]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

/-- **The generator of a finite shriek presentation is the free module sheaf on a sheafified
representable.** `AlgebraicGeometry.moduleShriekConstant` at `U` is the free module sheaf on
`h_U^#`, so the presentations of Stacks 095N are presentations by the objects of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves`.

The image of the terminal object of the small étale site of `U` under composition with `U ⟶ X` is
`AlgebraicGeometry.smallEtalePostcomposeFinalIso`-isomorphic to `U`, not equal to it. -/
public def moduleShriekConstantIsoFree (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type (u + 1)) [CommRing R] (U : SmallEtale B X.1 X.property) :
    moduleShriekConstant.{u, u + 1, u + 1} B X R U ≅
      (Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.free R)).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).obj U) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X R
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left R
  exact (Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree
      (smallEtalePostcompose B X.1 X.property U) _ _ R
      (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)).trans
    ((Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.free R)).mapIso
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.property)).mapIso
          (smallEtalePostcomposeFinalIso B X U)))

/-- **`j_{U!}\underline{\Lambda}_U` corepresents sections over `U`.** A morphism out of the
extension by zero at `U` of the constant free rank-one module sheaf is a section over `U`, as an
isomorphism of corepresented functors.

The ring universe is free here, where
`AlgebraicGeometry.moduleShriekConstantIsoFree` ties it to the module universe: this goes
through the constant-sheaf and sheaf-pullback adjunctions
(`CategoryTheory.Sheaf.coyonedaSheafPullbackConstantSheafIso`) followed by
`ModuleCat.coyonedaULiftSelfIso`, neither of which mentions `ModuleCat.free`, whose source
`Type r ⥤ ModuleCat.{r} R` is what forces the two universes together. The image of the terminal
object of the small étale site of `U` under composition with `U ⟶ X` is
`AlgebraicGeometry.smallEtalePostcomposeFinalIso`-isomorphic to `U`, not equal to it. -/
public def moduleShriekConstantCoyonedaIso (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [CommRing R] (U : SmallEtale B X.1 X.property) :
    coyoneda.obj (op (moduleShriekConstant.{u, r, w} B X R U)) ≅
      (sheafSections (SmallEtale.topology B X.1 X.property)
          (ModuleCat.{max (u + 1) r w} R)).obj (op U) ⋙
        forget (ModuleCat.{max (u + 1) r w} R) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B X R
  letI := SmallEtale.hasSheafify_moduleCat.{u, r, w} B U.obj.left R
  refine (Sheaf.coyonedaSheafPullbackConstantSheafIso.{u, u + 1, u, u + 1, r, max r w}
    (smallEtalePostcompose B X.1 X.property U)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property) R
    (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property)
    (ModuleCat.of R (ULift.{max (u + 1) w} R))).trans
      ((Functor.isoWhiskerLeft _
        (ModuleCat.coyonedaULiftSelfIso.{r, max (u + 1) w} R)).trans ?_)
  exact Functor.isoWhiskerRight
    (((sheafSections (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{max (u + 1) r w} R)).mapIso
        (smallEtalePostcomposeFinalIso B X U).op).symm)
    (forget (ModuleCat.{max (u + 1) r w} R))

/-- **Maps out of `j_{U!}\underline{\Lambda}_U` are sections over `U`.** A morphism from
`AlgebraicGeometry.moduleShriekConstant` at `U` into `F` is the same thing as a section of `F` over
`U`. This is what attaches a morphism of the presentations of Stacks 095N to each section, and the
small étale analogue of `Stacks.Sites.extensionUnitCoyonedaIso` for a ring sheaf. -/
public def moduleShriekConstantSectionEquiv (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [CommRing R] (U : SmallEtale B X.1 X.property)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r w} R)) :
    (moduleShriekConstant.{u, r, w} B X R U ⟶ F) ≃
      (forget (ModuleCat.{max (u + 1) r w} R)).obj (F.obj.obj (op U)) :=
  (Iso.app (moduleShriekConstantCoyonedaIso B X R U) F).toEquiv

/-- **Every sheaf of modules on the small étale site is a quotient of a direct sum of extensions
by zero of constant free rank-one module sheaves.** The direct sum runs over all pairs `(U, s)` of
an étale object and a section of `F` over it, and the component at `(U, s)` is the morphism that
`s` is under `AlgebraicGeometry.moduleShriekConstantSectionEquiv`.

This is the generation step of the proof of Stacks 095N — Stacks 093B part (2) read through Stacks
093C — in the spelling `AlgebraicGeometry.HasFiniteShriekPresentation` uses. What Stacks 095N needs
beyond it is that the étale objects may be taken affine, and that finitely many of them suffice. -/
public theorem epi_desc_moduleShriekConstant (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type (u + 1)) [CommRing R]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    [HasColimit (Discrete.functor fun p :
        Sheaf.Sections (SmallEtale.topology B X.1 X.property) R F =>
      moduleShriekConstant.{u, u + 1, u + 1} B X R p.1)] :
    Epi (Limits.Sigma.desc (fun p :
        Sheaf.Sections (SmallEtale.topology B X.1 X.property) R F =>
      (moduleShriekConstantSectionEquiv.{u, u + 1, u + 1} B X R p.1 F).symm p.2)) :=
  Sheaf.epi_desc_of_coyonedaSections (SmallEtale.topology B X.1 X.property) R _
    (fun U => moduleShriekConstantCoyonedaIso.{u, u + 1, u + 1} B X R U) F

end AlgebraicGeometry

end
