module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPushforwardQuasicoherent

/-!
# The transition of a pushforward on the total Zariski site is the base-change map

Let `f : V ⟶ U` be a morphism of simplicial schemes, `G` a sheaf of `𝒪_V`-modules on the total
Zariski site of `V`, and `φ : n ⟶ m` a map of simplicial degrees. The naturality square of `f`
at `φ`
```
  V_n --V φ--> V_m
   | f_n         | f_m
  U_n --U φ--> U_m
```
identifies the transition `(U φ)^* (f_*G)_m ⟶ (f_*G)_n` of the direct image with the
base-change morphism of the square followed by `f_{n,*}` of the transition of `G`, through the
identification `(f_*G)_k ≅ f_{k,*}(G_k)` of Stacks 09VP. Consequently that transition is an
isomorphism as soon as `G`'s transition at `φ` is, the square is a fibre square, `U φ` is flat
and `f_m` is quasi-compact and quasi-separated — which is Stacks 02KH.

## Main results

* `AlgebraicGeometry.SimplicialScheme.componentModuleDirectTransition_modulePushforward`: the
  direct transition of `f_*G` is `f_{m,*}` of the direct transition of `G`, read through the
  component identifications of Stacks 09VP and the comparison of the two composite direct
  images around the naturality square.
* `AlgebraicGeometry.SimplicialScheme.componentModuleTransition_modulePushforward`: the mate
  form, `(U φ)^*(f_*G)_m ⟶ (f_*G)_n` as the base-change morphism followed by `f_{n,*}` of the
  transition of `G`.
* `AlgebraicGeometry.SimplicialScheme.isIso_componentModuleTransition_modulePushforward`: that
  transition is an isomorphism under the hypotheses the source uses at a face map.

## Implementation notes

The first statement is proved on sections. Over an open `W` of `U_m` all three of the direct
transitions, the component identifications of Stacks 09VP and the comparison of the two
composite direct images are restriction maps of `G` — the first along the arrow of the total
Zariski site of `V` lying over `φ` above `f_m^{-1}W`, the last along the equality of opens
`f_n^{-1}(U φ)^{-1}W = (V φ)^{-1}f_m^{-1}W` supplied by the naturality square, and the middle
ones are the identity. Two arrows of the total site with the same source, the same target and
the same underlying map of simplicial degrees are equal, so the two composites agree.

The second statement is then formal: the mate of a composite is computed with the two
naturality rules for the adjunction `(U φ)^* ⊣ (U φ)_*`, the direct transition of `G` is the
unit followed by `(V φ)_*` of its own mate, and
`CategoryTheory.unit_mateEquiv_symm` turns the comparison of the composite direct images into
the base-change morphism, which is by definition its mate
(`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`).

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 09VP](https://stacks.math.columbia.edu/tag/09VP)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}} {n m : SimplexCategoryᵒᵖ}

/-- **The direct transition of a direct image is the direct image of the direct transition.**
Read through the identifications `(f_*G)_k ≅ f_{k,*}(G_k)` of Stacks 09VP and the comparison of
the two composite direct images around the naturality square of `f` at `φ`, the direct
transition of `f_*G` at `φ` is `f_{m,*}` of the direct transition of `G` at `φ`. -/
public theorem componentModuleDirectTransition_modulePushforward (f : V ⟶ U) (φ : n ⟶ m)
    (G : Modules V) :
    (componentModuleDirectTransition U φ).app ((modulePushforward f).obj G) ≫
        (Scheme.Modules.pushforward (U.map φ)).map
          ((componentModulePushforwardIso f G n).hom) =
      (componentModulePushforwardIso f G m).hom ≫
        (Scheme.Modules.pushforward (f.app m)).map
            ((componentModuleDirectTransition V φ).app G) ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
            (f.naturality φ)).hom.app ((componentModule V n).obj G) := by
  ext W x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  have e : (f.app n ≫ U.map φ) ⁻¹ᵁ W = (V.map φ ≫ f.app m) ⁻¹ᵁ W :=
    congrArg (fun k : V.obj n ⟶ U.obj m => k ⁻¹ᵁ W) (f.naturality φ).symm
  have key : (zariskiPullback f).map (SimplicialSheafSystem.transitionHom φ W) =
      (levelFunctor (zariskiSpace V) n).map (eqToHom e) ≫
        SimplicialSheafSystem.transitionHom (X := zariskiSpace V) φ
          ((Opens.map (f.app m).base).obj W) := by
    apply SimplicialOpen.Hom.ext
    change φ = (𝟙 n) ≫ φ
    simp
  change (G.val.presheaf.map ((zariskiPullback f).map
      (SimplicialSheafSystem.transitionHom φ W)).op) x =
    (G.val.presheaf.map ((levelFunctor (zariskiSpace V) n).map (eqToHom e)).op)
      ((G.val.presheaf.map (SimplicialSheafSystem.transitionHom (X := zariskiSpace V) φ
        ((Opens.map (f.app m).base).obj W)).op) x)
  refine Eq.trans (congrArg (fun a => (G.val.presheaf.map (Quiver.Hom.op a)) x) key) ?_
  have hcomp := G.val.presheaf.map_comp
    (SimplicialSheafSystem.transitionHom (X := zariskiSpace V) φ
      ((Opens.map (f.app m).base).obj W)).op
    ((levelFunctor (zariskiSpace V) n).map (eqToHom e)).op
  exact congr($hcomp x)

/-- **The transition of a direct image is the base-change morphism.** Read through the
identifications `(f_*G)_k ≅ f_{k,*}(G_k)` of Stacks 09VP, the transition
`(U φ)^*(f_*G)_m ⟶ (f_*G)_n` of `f_*G` at `φ` is the base-change morphism of the naturality
square of `f` at `φ` followed by `f_{n,*}` of the transition of `G` at `φ`. -/
public theorem componentModuleTransition_modulePushforward (f : V ⟶ U) (φ : n ⟶ m)
    (G : Modules V) :
    componentModuleTransition U φ ((modulePushforward f).obj G) ≫
        (componentModulePushforwardIso f G n).hom =
      (Scheme.Modules.pullback (U.map φ)).map ((componentModulePushforwardIso f G m).hom) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
            (f.naturality φ)).app ((componentModule V m).obj G) ≫
          (Scheme.Modules.pushforward (f.app n)).map (componentModuleTransition V φ G) := by
  have hd : (componentModuleDirectTransition V φ).app G =
      (Scheme.Modules.pullbackPushforwardAdjunction (V.map φ)).unit.app
          ((componentModule V m).obj G) ≫
        (Scheme.Modules.pushforward (V.map φ)).map (componentModuleTransition V φ G) :=
    (Equiv.apply_symm_apply
        ((Scheme.Modules.pullbackPushforwardAdjunction (V.map φ)).homEquiv _ _) _).symm.trans
      (Adjunction.homEquiv_unit _ _ _ _)
  have hnat : (Scheme.Modules.pushforward (f.app m)).map
          ((Scheme.Modules.pushforward (V.map φ)).map (componentModuleTransition V φ G)) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
          (f.naturality φ)).hom.app ((componentModule V n).obj G) =
      (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
            (f.naturality φ)).hom.app
          ((Scheme.Modules.pullback (V.map φ)).obj ((componentModule V m).obj G)) ≫
        (Scheme.Modules.pushforward (U.map φ)).map
          ((Scheme.Modules.pushforward (f.app n)).map (componentModuleTransition V φ G)) :=
    (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
      (f.naturality φ)).hom.naturality (componentModuleTransition V φ G)
  have hPsi : (Scheme.Modules.pushforward (f.app m)).map
          ((componentModuleDirectTransition V φ).app G) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
          (f.naturality φ)).hom.app ((componentModule V n).obj G) =
      (Scheme.Modules.pullbackPushforwardAdjunction (U.map φ)).unit.app
          ((Scheme.Modules.pushforward (f.app m)).obj ((componentModule V m).obj G)) ≫
        (Scheme.Modules.pushforward (U.map φ)).map
            ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
              (f.naturality φ)).app ((componentModule V m).obj G)) ≫
          (Scheme.Modules.pushforward (U.map φ)).map
            ((Scheme.Modules.pushforward (f.app n)).map
              (componentModuleTransition V φ G)) := by
    rw [hd, Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
      unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction (V.map φ))
        (Scheme.Modules.pullbackPushforwardAdjunction (U.map φ))
        (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
          (f.naturality φ)).hom ((componentModule V m).obj G),
      Category.assoc]
    rfl
  have hsymmPsi : ((Scheme.Modules.pullbackPushforwardAdjunction (U.map φ)).homEquiv _ _).symm
        ((Scheme.Modules.pushforward (f.app m)).map
            ((componentModuleDirectTransition V φ).app G) ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
            (f.naturality φ)).hom.app ((componentModule V n).obj G)) =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
          (f.naturality φ)).app ((componentModule V m).obj G) ≫
        (Scheme.Modules.pushforward (f.app n)).map (componentModuleTransition V φ G) := by
    rw [hPsi, ← Functor.map_comp]
    exact Equiv.symm_apply_apply _ _
  refine Eq.trans ((Scheme.Modules.pullbackPushforwardAdjunction
      (U.map φ)).homEquiv_naturality_right_symm
      ((componentModuleDirectTransition U φ).app ((modulePushforward f).obj G))
      ((componentModulePushforwardIso f G n).hom)).symm ?_
  rw [componentModuleDirectTransition_modulePushforward f φ G,
    Adjunction.homEquiv_naturality_left_symm, hsymmPsi]

/-- **The cartesian condition for a direct image, at one map of simplicial degrees.** Let
`f : V ⟶ U` be a cartesian morphism of simplicial schemes and `φ : n ⟶ m` a map of degrees such
that `U φ` is flat and `f_m` is quasi-compact and quasi-separated. If the degree-`m` component
of `G` is quasi-coherent and the transition of `G` at `φ` is an isomorphism, then so is the
transition of `f_*G` at `φ`. -/
public theorem isIso_componentModuleTransition_modulePushforward (f : V ⟶ U)
    (hf : NatTrans.Equifibered f) (φ : n ⟶ m) [Flat (U.map φ)]
    [QuasiCompact (f.app m)] [QuasiSeparated (f.app m)] (G : Modules V)
    [((componentModule V m).obj G).IsQuasicoherent]
    (hG : IsIso (componentModuleTransition V φ G)) :
    IsIso (componentModuleTransition U φ ((modulePushforward f).obj G)) := by
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (f.naturality φ)).app ((componentModule V m).obj G)) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      (hf φ) ((componentModule V m).obj G)
  have hcomp : IsIso (componentModuleTransition U φ ((modulePushforward f).obj G) ≫
      (componentModulePushforwardIso f G n).hom) := by
    rw [componentModuleTransition_modulePushforward]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (componentModulePushforwardIso f G n).hom

end AlgebraicGeometry.SimplicialScheme

end
