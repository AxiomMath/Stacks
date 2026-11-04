module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.Topology.Simplicial.Morphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.Topology.Simplicial.Sheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# The Zariski ringed topos of a simplicial scheme, and pullback of modules

For a simplicial scheme `X` the total Zariski site `X_Zar` has as objects the open subsets of
the schemes `X n`, one simplicial degree at a time, and as coverings the levelwise open
coverings. The structure sheaf has sections `Γ(X n, W)` over the object `(n, W)`, with
restriction maps induced by the scheme morphisms `X φ`. A morphism of simplicial schemes
`f : V ⟶ U` induces a morphism of the resulting ringed topoi, and therefore a pullback functor
`f^*` on sheaves of modules; Stacks 07TI asserts that `f^*` preserves quasi-coherence.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.ZariskiOpen` and `.zariskiTopology`: the total Zariski
  site of a simplicial scheme, as the site of its underlying simplicial space.
* `AlgebraicGeometry.SimplicialScheme.structureSheaf`: the structure sheaf `𝒪_X` of `X_Zar`.
* `AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos`: the pair `(X_Zar, 𝒪_X)`.
* `AlgebraicGeometry.SimplicialScheme.zariskiSharp` and `.zariskiRingedToposHom`: the structure
  map `f♯` of a morphism of simplicial schemes and the morphism of ringed topoi it defines.
* `AlgebraicGeometry.SimplicialScheme.Modules` and `.modulePullback`: sheaves of `𝒪_X`-modules
  on `X_Zar` and the pullback `f^*` along a morphism of simplicial schemes.

## Main results

* `AlgebraicGeometry.SimplicialScheme.structurePresheaf_isSheaf`: the presheaf of section rings
  on the total site is a sheaf.
* `AlgebraicGeometry.SimplicialScheme.structureComponentIso`: in each degree it is the ordinary
  structure presheaf of the scheme in that degree.
* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePullback_of_presentation`:
  **Stacks 07TI for a globally presented module.** The pullback of a sheaf of `𝒪_U`-modules
  admitting a global presentation on `U_Zar` is quasi-coherent on `V_Zar`.

## Implementation notes

The underlying site is the site of a simplicial topological space of Stacks 09VL, applied to the
underlying simplicial space, so its coverings and the morphism of sites induced by a morphism of
simplicial schemes are the ones of Stacks 09VL and Stacks 09VN. The sheaf condition for the
presheaf of section rings is obtained from the description of sheaves on that site as systems of
degreewise sheaves, Stacks 09VM: the degreewise structure sheaves of the schemes with transition
maps `X φ` form such a system, and the presheaf reconstructed from it is identified with the
explicit presheaf of section rings.

That identification is a naturality square between two presheaves whose values agree only after
unfolding both the opaque reconstruction functor of Stacks 09VM and the inclusion of a single
simplicial degree. Rewriting inside it is therefore not possible: the intermediate terms are not
type-correct at reducible transparency. It is proved instead by naming the intermediate open of
the factorization of a morphism of the total site — a levelwise inclusion followed by a
transition — as an explicit pair, and composing the naturality of the component identification
with the compatibility of the reconstructed restriction maps as a chain of `Eq.trans` and
`congrArg` in term mode, where every step is checked at default transparency. The structure map
`f♯` is pinned down the same way, by composing the two `appLE` factorizations rather than
normalizing them with `simp`.

**What is proved of Stacks 07TI here and what is not.** The source deduces 07TI from
Stacks 0D7M, which identifies the quasi-coherent modules on a total site with the cartesian
modules having quasi-coherent components. That equivalence is available, at
`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_iff_isCartesianModule_and_components`,
and so is 07TI in full, at
`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePullback`; neither was when this
file was written. The route taken here is the general preservation statement of Stacks 03DO for a
morphism of ringed topoi, and the development has that statement only for a module with a
*global* presentation
(`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_presentation`), which
is what is specialized below. Passing from a global presentation to the merely local one that
quasi-coherence records needs the localization of the morphism at an object, Stacks 04J0, and
the development has that only for a morphism of ringed *sites* between sites having all finite
limits (`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos`). The total
Zariski site has no final object — a terminal object would have to lie in a degree admitting a
unique simplex map from every other degree, and no degree does — so that statement does not
apply to it, and its hypotheses are not merely unverified here but false. Closing 07TI in full
therefore needs either 0D7M or a form of Stacks 04J0 that asks for a covering of the final
object as a hypothesis instead of deriving it from terminality.

## References

* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 09VN](https://stacks.math.columbia.edu/tag/09VN)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-- The simplicial topological space underlying a simplicial scheme. -/
public abbrev zariskiSpace (X : SimplicialObject Scheme.{u}) : SimplicialObject TopCat.{u} :=
  X ⋙ Scheme.forgetToTop

/-- An object of the total Zariski site of a simplicial scheme: an open subset of the scheme in
one simplicial degree. -/
public abbrev ZariskiOpen (X : SimplicialObject Scheme.{u}) := SimplicialOpen (zariskiSpace X)

/-- The topology of levelwise Zariski open coverings on the total Zariski site. -/
public abbrev zariskiTopology (X : SimplicialObject Scheme.{u}) :=
  SimplicialOpen.grothendieckTopology (zariskiSpace X)

/-- The presheaf of section rings `Γ(X n, W)` on the total Zariski site, with restriction maps
induced by the morphisms of the simplicial scheme. -/
public def structurePresheaf (X : SimplicialObject Scheme.{u}) :
    (ZariskiOpen X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := (X.obj U.unop.degree).presheaf.obj (op U.unop.toOpens)
  map {U V} f := (X.map f.unop.base).appLE U.unop.toOpens V.unop.toOpens
    (SimplicialOpen.Hom.le f.unop)
  map_id U := by
    refine (Stacks.AffineAlgebraEquivalence.appLE_congr_hom
      (X.map_id U.unop.degree) _ le_rfl).trans ?_
    change 𝟙 _ ≫ (X.obj U.unop.degree).presheaf.map (𝟙 _) = _
    exact (Category.id_comp _).trans ((X.obj U.unop.degree).presheaf.map_id _)
  map_comp {U V W} f g :=
    (Stacks.AffineAlgebraEquivalence.appLE_congr_hom
        (X.map_comp g.unop.base f.unop.base) _ _).trans
      (Scheme.Hom.appLE_comp_appLE (X.map g.unop.base) (X.map f.unop.base) _ _ _ _ _).symm

/-- In each simplicial degree the presheaf of section rings is the structure presheaf of the
scheme in that degree. -/
public def structureComponentIso (X : SimplicialObject Scheme.{u}) (n : SimplexCategoryᵒᵖ) :
    componentPresheaf (structurePresheaf X) n ≅ (X.obj n).presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {U V} f => by
    change (X.map (𝟙 n)).appLE _ _ _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id]
    refine (Stacks.AffineAlgebraEquivalence.appLE_congr_hom (X.map_id n) _ f.unop.le).trans ?_
    rfl)

/-- The degreewise structure sheaves of a simplicial scheme, with transition maps induced by the
morphisms of the simplicial scheme: a system of sheaves in the sense of Stacks 09VM. -/
public def structureSystem (X : SimplicialObject Scheme.{u}) :
    SimplicialSheafSystem (zariskiSpace X) CommRingCat.{u} where
  component n := (X.obj n).sheaf
  transition φ := StacksFMap.ofPresheafHom (X.map φ).c
  transition_id n V := by
    change HEq ((X.map (𝟙 n)).app V.unop) (𝟙 _)
    rw [X.map_id]
    rfl
  transition_comp φ ψ V := by
    change HEq ((X.map ψ).app V.unop ≫ (X.map φ).app _)
      ((X.map (φ ≫ ψ)).app V.unop)
    rw [X.map_comp]
    rfl

/-- The presheaf reconstructed from the system of degreewise structure sheaves is the presheaf
of section rings. -/
public noncomputable def reconstructedStructureIso (X : SimplicialObject Scheme.{u}) :
    (sheafEquivalenceSimplicialSheafSystem (zariskiSpace X) CommRingCat.{u}).toPresheaf.obj
      (structureSystem X) ≅ structurePresheaf X := by
  let E := sheafEquivalenceSimplicialSheafSystem (zariskiSpace X) CommRingCat.{u}
  let S := structureSystem X
  let R := E.toPresheaf.obj S
  refine NatIso.ofComponents
    (fun U => ((E.componentIso U.unop.degree).app S).app (op U.unop.toOpens)) ?_
  intro U V f
  let φ := f.unop.base
  let pre : Opens ((zariskiSpace X).obj V.unop.degree) :=
    (Opens.map ((zariskiSpace X).map φ)).obj U.unop.toOpens
  let mid : ZariskiOpen X := ⟨V.unop.degree, pre⟩
  let i : V.unop.toOpens ⟶ pre := homOfLE (SimplicialOpen.Hom.le f.unop)
  let a : V.unop ⟶ mid := (levelFunctor (zariskiSpace X) V.unop.degree).map i
  let b : mid ⟶ U.unop := SimplicialSheafSystem.transitionHom φ U.unop.toOpens
  have hf : f.unop = a ≫ b := SimplicialOpen.Hom.ext _ _ (Category.id_comp _).symm
  have h1 : f = b.op ≫ a.op := Quiver.Hom.unop_inj hf
  have hR : R.map f = R.map b.op ≫ R.map a.op :=
    (congrArg (fun k : U ⟶ V => R.map k) h1).trans (R.map_comp b.op a.op)
  let θV := ((E.componentIso V.unop.degree).app S).hom.app (op V.unop.toOpens)
  let θP := ((E.componentIso V.unop.degree).app S).hom.app (op pre)
  let θU := ((E.componentIso U.unop.degree).app S).hom.app (op U.unop.toOpens)
  let tr := (S.transition φ).app (op U.unop.toOpens)
  let ri := (X.obj V.unop.degree).presheaf.map i.op
  have hn : R.map a.op ≫ θV = θP ≫ ri :=
    ((E.componentIso V.unop.degree).app S).hom.naturality i.op
  have ht : R.map b.op ≫ θP = θU ≫ tr :=
    E.transition_compatibility S φ (op U.unop.toOpens)
  have hlast : tr ≫ ri = (structurePresheaf X).map f := rfl
  exact (congrArg (fun k => k ≫ θV) hR).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => R.map b.op ≫ k) hn).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ ri) ht).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun k => θU ≫ k) hlast))))))

/-- The presheaf of section rings on the total Zariski site is a sheaf. -/
public theorem structurePresheaf_isSheaf (X : SimplicialObject Scheme.{u}) :
    Presheaf.IsSheaf (zariskiTopology X) (structurePresheaf X) := by
  let E := sheafEquivalenceSimplicialSheafSystem (zariskiSpace X) CommRingCat.{u}
  let S := structureSystem X
  let Q := E.toEquivalence.inverse.obj S
  let e : Q.obj ≅ structurePresheaf X :=
    (E.underlyingPresheafIso.app Q).symm ≪≫
      E.toPresheaf.mapIso (E.toEquivalence.counitIso.app S) ≪≫ reconstructedStructureIso X
  exact (Presheaf.isSheaf_of_iso_iff e).mp Q.property

/-- The structure sheaf `𝒪_X` of the total Zariski site of a simplicial scheme. -/
public noncomputable def structureSheaf (X : SimplicialObject Scheme.{u}) :
    Sheaf (zariskiTopology X) CommRingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- The total Zariski site of a simplicial scheme is essentially small in the universe of the
schemes: it has a type of objects in that universe and all its morphism types are small. -/
public instance essentiallySmall_zariskiOpen (X : SimplicialObject Scheme.{u}) :
    EssentiallySmall.{u} (ZariskiOpen X) :=
  essentiallySmall_of_small_of_locallySmall (ZariskiOpen X)

/-- The Zariski ringed topos `(X_Zar, 𝒪_X)` of a simplicial scheme.

Reducible, so that instance search sees through its three projections. Without that, `𝒪_X`
restricted to a slice of the total site carries the topology spelled `(zariskiRingedTopos X).J`
on the category spelled `(zariskiRingedTopos X).C`, while every site-level fact about the total
Zariski site is stated at `zariskiTopology X` on `ZariskiOpen X`; the two are definitionally
equal, instance synthesis runs at a transparency that does not unfold a plain `def`, and an
instance stated in one spelling is then never found for a goal in the other. -/
@[reducible]
public noncomputable def zariskiRingedTopos (X : SimplicialObject Scheme.{u}) :
    RingedTopos.{0, u, u} where
  C := ZariskiOpen X
  J := zariskiTopology X
  O := structureSheaf X

/-- The structure sheaf of the Zariski ringed topos of `X` is `structureSheaf X`. -/
@[simp]
public theorem zariskiRingedTopos_O (X : SimplicialObject Scheme.{u}) :
    (zariskiRingedTopos X).O = structureSheaf X := rfl

variable {V U : SimplicialObject Scheme.{u}}

/-- The degreewise inverse image of open subsets along a morphism of simplicial schemes. -/
public def zariskiPullback (f : V ⟶ U) : ZariskiOpen U ⥤ ZariskiOpen V :=
  SimplicialOpen.pullback (Functor.whiskerRight f Scheme.forgetToTop)

/-- Degreewise inverse image of opens is continuous for the levelwise Zariski topologies; it is
in fact a morphism of sites, by Stacks 09VN. -/
public instance zariskiPullback_isContinuous (f : V ⟶ U) :
    (zariskiPullback f).IsContinuous (zariskiTopology U) (zariskiTopology V) :=
  (SimplicialOpen.pullback_isMorphismOfSites
    (Functor.whiskerRight f Scheme.forgetToTop)).toIsContinuous

/-- The structure map `f♯ : 𝒪_U ⟶ f_*𝒪_V` of a morphism of simplicial schemes: on the open
`(n, W)` it is the map `f n` induces on sections. -/
public noncomputable def zariskiSharp (f : V ⟶ U) :
    structureSheaf U ⟶ ((zariskiPullback f).sheafPushforwardContinuous CommRingCat.{u}
      (zariskiTopology U) (zariskiTopology V)).obj (structureSheaf V) where
  hom :=
    { app W := (f.app W.unop.degree).app W.unop.toOpens
      naturality A B g := by
        change (U.map g.unop.base).appLE _ _ _ ≫ (f.app B.unop.degree).app _ =
          (f.app A.unop.degree).app _ ≫ (V.map g.unop.base).appLE _ _ _
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
        refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
          (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
        exact Stacks.AffineAlgebraEquivalence.appLE_congr_hom
          (f.naturality g.unop.base).symm _ _ }

/-- Abelian sheafification exists on the total Zariski site, because the site is essentially
small. -/
public instance zariski_hasSheafify (X : SimplicialObject Scheme.{u}) :
    HasSheafify (zariskiTopology X) AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact hasSheafifyEssentiallySmallSite (zariskiTopology X) AddCommGrpCat.{u}

/-- Abelian sheafification on the total Zariski site inverts exactly the locally bijective
morphisms. -/
public instance zariski_wEqualsLocallyBijective (X : SimplicialObject Scheme.{u}) :
    (zariskiTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let : CategoryTheory.Limits.PreservesLimits (forget AddCommGrpCat.{u}) :=
    AddCommGrpCat.forget_preservesLimits
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (A := AddCommGrpCat.{u}) (zariskiTopology X)

/-- The morphism of Zariski ringed topoi `f_Zar : (V_Zar, 𝒪_V) ⟶ (U_Zar, 𝒪_U)` attached to a
morphism of simplicial schemes `f : V ⟶ U`: the geometric morphism is the one induced by the
degreewise inverse image of opens, and the structure map is `f♯`. -/
public noncomputable def zariskiRingedToposHom (f : V ⟶ U) :
    RingedToposHom (zariskiRingedTopos V) (zariskiRingedTopos U) where
  toToposHom := (SimplicialOpen.pullback_isMorphismOfSites.{u}
    (Functor.whiskerRight f Scheme.forgetToTop)).morphismOfTopoi
  fSharp := zariskiSharp f ≫ (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
    (zariskiTopology U) (zariskiTopology V) (zariskiPullback f) (structureSheaf V)).inv

/-- Sheaves of modules on the Zariski ringed topos of a simplicial scheme. -/
public noncomputable abbrev Modules (X : SimplicialObject Scheme.{u}) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)

/-- Pullback of sheaves of modules along a morphism of simplicial schemes: the inverse image
followed by extension of scalars along `f♯`. -/
public noncomputable def modulePullback (f : V ⟶ U) : Modules U ⥤ Modules V :=
  (zariskiRingedToposHom f).toRingedToposModulesHom.pullbackModules

/-- **Stacks 07TI for a globally presented module.** For a morphism of simplicial schemes
`f : V ⟶ U` and a sheaf of `𝒪_U`-modules on `U_Zar` admitting a global presentation, the
pullback `f^*F` is a quasi-coherent sheaf of `𝒪_V`-modules on `V_Zar`. -/
@[stacks 07TI "for a module admitting a GLOBAL presentation on the total Zariski site, a \
strengthening of the source's hypothesis that it be quasi-coherent, i.e. presented only \
locally. The source's statement is proved in full at \
`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePullback`, through the \
localization 04J0 of a morphism of ringed sites at an object on the equi-universe model of the \
total Zariski site; this is the direct specialization of 03DO, which needs no localization"]
public theorem isQuasicoherentOnSite_modulePullback_of_presentation (f : V ⟶ U)
    {F : Modules U} (P : F.Presentation) :
    ((modulePullback f).obj F).IsQuasicoherentOnSite :=
  Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_presentation
    (zariskiRingedToposHom f).toRingedToposModulesHom P

end AlgebraicGeometry.SimplicialScheme

end
