module

public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialSurjectivity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
import StacksCore.Tactic.StacksAttribute

/-!
# Components of the pushforward of a module on the Zariski site of a simplicial scheme

For a morphism `f : V ⟶ U` of simplicial schemes the degree-`n` component of the pushforward
`f_*G` of a sheaf of modules on the total Zariski site is the pushforward of the degree-`n`
component of `G` along the morphism of schemes `f_n : V_n ⟶ U_n`. When `f_n` is quasi-compact
and quasi-separated and `G_n` is quasi-coherent, the component `(f_*G)_n` is therefore a
quasi-coherent `𝒪_{U_n}`-module.

## Main results

* `Stacks.Sheaves.RingedToposModules.pushforwardModules_add_natTrans` and
  `.pushforwardModules_smul_natTrans`: the addition and the scalar action on the sections of a
  direct image of sheaves of modules along a morphism of ringed topoi, read through a natural
  transformation out of `f_* ⋙ Γ(·)` into the sections over a single object of the source site.
* `AlgebraicGeometry.SimplicialScheme.componentModulePushforwardIso`: **Stacks 09VP part (1)
  for sheaves of modules on the total Zariski site.** `(f_*G)_n ≅ f_{n,*}(G_n)`.
* `AlgebraicGeometry.SimplicialScheme.isQuasicoherent_componentModule_modulePushforward`:
  **Stacks 07TJ for the components.** If `f_n` is quasi-compact and quasi-separated and `G_n`
  is quasi-coherent, then `(f_*G)_n` is quasi-coherent.

## Implementation notes

The direct image of sheaves of modules on the total Zariski site is the one of Stacks 03D6 for
a morphism of ringed topoi: its underlying sheaf of abelian groups is the geometric direct
image, but its addition and scalar action are the ones *transported* along the direct image by
the product comparisons of Stacks 03D1, so neither agrees on the nose with the pointwise
operations of the scheme-level pushforward of
`AlgebraicGeometry.Scheme.Modules.pushforward`, which is Mathlib's pushforward along the
continuous functor of inverse images of opens. The two sheaves of *sets* underlying the two
components do agree on the nose, which is why the comparison is the identity on sections and
is produced by `Stacks.Sheaves.PushforwardEssentialImage.isoOfSheafHom`; its content is
exactly that the two additions and the two scalar actions agree.

Those two agreements are the two general lemmas proved first. They are stated for an arbitrary
natural transformation `θ : f_* ⋙ Γ(Z, ·) ⟶ Γ(Z', ·)` rather than for the sections functors of
the Zariski site directly: the identification of `f_*(-)` evaluated at `Z` with evaluation at
the inverse image `Z'` holds on the nose for a morphism of topoi coming from a continuous
functor, so the transformation is applied as the identity, but the intermediate functor
`f_* ⋙ Γ(Z, ·)` does not get a `PreservesFiniteProducts` instance in the Zariski case, because
the site of `AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos` is reached through a
projection that instance search does not unfold. In the general statement the site is a
variable, the instance is found, and the specialization needs none.

## References

* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 09VP](https://stacks.math.columbia.edu/tag/09VP)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial

namespace Stacks.Sheaves.RingedToposModules

open _root_.AlgebraicGeometry

universe w v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : RingedToposHom X Y) (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The addition on the sections over `Z` of a direct image of sheaves of modules is the
addition of the original module, read through any natural transformation from `f_*(-)` evaluated
at `Z` to the sections over an object `Z'` of the source site. -/
public theorem pushforwardModules_add_natTrans (Z : Y.Cᵒᵖ) (Z' : X.Cᵒᵖ)
    (θ : f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z ⟶
      Sheaf.sectionsFunctor X.J Z')
    (x y : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M))) :
    θ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) (x + y) =
      θ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) x +
        θ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) y := by
  rw [pushforwardModules_add]
  exact Eq.trans
    (Sheaf.moduleAddObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M θ x y)
    (Sheaf.sectionsFunctor_map_moduleAddHom _ M _ _ _)

/-- The scalar action on the sections over `Z` of a direct image of sheaves of modules is the
action of the original module on its sections over an object `Z'` of the source site, with the
scalar carried along the direct-image form `f♯` of the structure map, read through any natural
transformation from `f_*(-)` evaluated at `Z` to the sections over `Z'`.

The transported scalar is taken as a parameter `s` together with the identification `hs`, so
that the conclusion can be read with the scalar in whatever form the application has it. -/
public theorem pushforwardModules_smul_natTrans (Z : Y.Cᵒᵖ) (Z' : X.Cᵒᵖ)
    (θ : f.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J Z ⟶
      Sheaf.sectionsFunctor X.J Z')
    (r : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (x : (Sheaf.sectionsFunctor Y.J Z).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj M)))
    (s : (Sheaf.sectionsFunctor X.J Z').obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hs : θ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((Sheaf.sectionsFunctor Y.J Z).map (fSharpSet f) r) = s) :
    θ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) (r • x) =
      s • θ.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) x := by
  rw [pushforwardModules_smul_fSharpSet, ← hs]
  exact Eq.trans
    (Sheaf.moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M θ _ x)
    (Sheaf.sectionsFunctor_map_moduleSMulHom _ M _ _ _)

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.SimplicialScheme

open Stacks.Sheaves.RingedToposModules

universe u

variable {V U : SimplicialObject Scheme.{u}}

/-- The structure map `f♯` of the morphism of Zariski ringed topoi attached to a morphism of
simplicial schemes acts on sections over an open `(n, W)` as the map `f_n` induces on sections
over `W`. -/
public theorem fSharpSet_sections (f : V ⟶ U) (W : (ZariskiOpen U)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos U).O).obj.obj W) :
    (Sheaf.sectionsFunctor.{u} (zariskiTopology U) W).map
        (fSharpSet (zariskiRingedToposHom f).toRingedToposModulesHom) r =
      (f.app W.unop.degree).app W.unop.toOpens r := by
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor.{u} (zariskiTopology U) W).map m r)
    (_root_.AlgebraicGeometry.RingedToposHom.ringFsharp_forget (zariskiRingedToposHom f))) ?_
  rfl

/-- **Stacks 09VP, part (1), for sheaves of modules on the total Zariski site.** The degree-`n`
component of the pushforward of a sheaf of `𝒪_V`-modules along a morphism `f : V ⟶ U` of
simplicial schemes is the pushforward of its degree-`n` component along `f_n : V_n ⟶ U_n`. -/
@[stacks 09VP "part (1) for sheaves of modules on the total Zariski site of a simplicial scheme"]
public noncomputable def componentModulePushforwardIso (f : V ⟶ U) (G : Modules V)
    (n : SimplexCategoryᵒᵖ) :
    (componentModule U n).obj ((modulePushforward f).obj G) ≅
      (Scheme.Modules.pushforward (f.app n)).obj ((componentModule V n).obj G) :=
  Stacks.Sheaves.PushforwardEssentialImage.isoOfSheafHom
    (R := (U.obj n).ringCatSheaf)
    (M := (componentModule U n).obj ((modulePushforward f).obj G))
    (N := (Scheme.Modules.pushforward (f.app n)).obj ((componentModule V n).obj G))
    (𝟙 _) (IsIso.id _)
    (fun Z x y ↦ pushforwardModules_add_natTrans
      (zariskiRingedToposHom f).toRingedToposModulesHom G (op ⟨n, Z.unop⟩)
      (op ((zariskiPullback f).obj ⟨n, Z.unop⟩)) (𝟙 _) x y)
    (fun Z r x ↦ pushforwardModules_smul_natTrans
      (zariskiRingedToposHom f).toRingedToposModulesHom G (op ⟨n, Z.unop⟩)
      (op ((zariskiPullback f).obj ⟨n, Z.unop⟩)) (𝟙 _) r x
      ((f.app n).app Z.unop r) (fSharpSet_sections f (op ⟨n, Z.unop⟩) r))

/-- **Stacks 07TJ for the components of the pushforward.** Let `f : V ⟶ U` be a morphism of
simplicial schemes and `G` a sheaf of `𝒪_V`-modules on the total Zariski site. If `f_n` is
quasi-compact and quasi-separated and the degree-`n` component `G_n` is a quasi-coherent
`𝒪_{V_n}`-module, then the degree-`n` component `(f_*G)_n` of the pushforward is a
quasi-coherent `𝒪_{U_n}`-module. -/
@[stacks 07TJ "the quasi-coherence of the COMPONENTS of the pushforward only: `(f_*G)_n` is a \
quasi-coherent module on `U_n` as soon as `f_n` is quasi-compact and quasi-separated and `G_n` \
is quasi-coherent. This is the source's identification `F_n = f_{n,*}G_n` (09VP, here \
`componentModulePushforwardIso`) together with 01LC, and it needs neither the cartesian \
hypothesis on `f` nor the flatness of the face maps of `U`. What is NOT proved is that `f_*G` \
is quasi-coherent on the total Zariski site: the source gets that from 0D7M, of which this \
development has only the right-hand side \
(`CategoryTheory.SimplicialSiteSituation.IsCartesianWithQuasicoherentComponents`, neither \
direction of the equivalence), and the other half of that right-hand side -- that `f_*G` is \
cartesian, which is where 02KH and the flatness of the face maps enter -- cannot even be \
stated here, the development carrying no cartesian-module predicate for the total Zariski \
site of a simplicial scheme"]
public theorem isQuasicoherent_componentModule_modulePushforward (f : V ⟶ U)
    (n : SimplexCategoryᵒᵖ) [QuasiCompact (f.app n)] [QuasiSeparated (f.app n)]
    (G : Modules V) [((componentModule V n).obj G).IsQuasicoherent] :
    ((componentModule U n).obj ((modulePushforward f).obj G)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (U.obj n).ringCatSheaf).prop_of_iso
    (componentModulePushforwardIso f G n).symm inferInstance

end AlgebraicGeometry.SimplicialScheme

end
