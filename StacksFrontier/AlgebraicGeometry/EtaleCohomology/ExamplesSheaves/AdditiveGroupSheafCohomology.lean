module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSiteAssociatedModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of `Gₐ` agrees on the big sites and is the cohomology of `𝒪_X`

Let `S` be a scheme below the cutoff of a big `τ`-site. For all `p ≥ 0` there are isomorphisms

```
H^p_{fppf}(X, Gₐ) = H^p_{étale}(X, Gₐ) = H^p_{Zar}(X, Gₐ) = H^p(X, 𝒪_X)
```

where `H^p(X, 𝒪_X)` is the cohomology of the structure sheaf on the underlying topological space
of `S`. They are the specialization to `ℱ = 𝒪_S` of the comparison `H^p(S, ℱ) ≅ H^p_τ(S, ℱᵃ)`
between the cohomology of a quasi-coherent module and the `τ`-cohomology of its associated
module, combined with the identification `Gₐ ≅ (𝒪_S)ᵃ`.

## Main definitions

* `AlgebraicGeometry.quasiCoherentPresheafUnitIso`: the presheaf of [Stacks, Tag 03DS] at
  `𝒪_S` is the presheaf of global functions, read additively.
* `AlgebraicGeometry.overAdditiveGroupSheaf`: `Gₐ` on the localized big `τ`-site of `S`,
  uniform in `τ`.
* `AlgebraicGeometry.overAdditiveGroupSheafIsoAssociatedSheaf`: `Gₐ ≅ (𝒪_S)ᵃ` as abelian
  sheaves on that site.
* `AlgebraicGeometry.additiveGroupSheafCohomologyIso`: `H^p(X, 𝒪_X) ≅ H^p_τ(X, Gₐ)` for every
  `p` and every big site.
* `AlgebraicGeometry.additiveGroupSheafCohomologyFppfEtaleIso` and
  `AlgebraicGeometry.additiveGroupSheafCohomologyFppfZariskiIso`:
  `H^p_{fppf}(X, Gₐ) ≅ H^p_{étale}(X, Gₐ)` and `H^p_{fppf}(X, Gₐ) ≅ H^p_{Zar}(X, Gₐ)` for every
  `p`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Adequate
open scoped AlgebraicGeometry

universe u

-- The `Ext` universe and enough injectives of a localized big site, which is essentially small at
-- the universe of its morphisms.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

namespace AlgebraicGeometry

/-! ### Global sections over `⊤`, functorially -/

/-- Global sections over `⊤`, as a functor on the modules of a scheme: the abelian sheaf
underlying a module, evaluated at `⊤`. -/
alias sectionsTopFunctor := globalSectionsGroup

/-- The presheaf of global functions on the schemes over `S`, read additively:
`T ↦ Γ(T, 𝒪_T)`. -/
@[sga "3 I 4.3.1"]
public abbrev globalFunctionsAddPresheaf (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat.{u}

/-! ### Naturality of `Γ(T, T^* 𝒪_S) ≅ Γ(T, 𝒪_T)` -/

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X`, read on global sections and restricted along any
`i : ⊤ ⟶ f ⁻¹ᵁ ⊤`, is the ring map `f.appTop` on global functions. -/
public theorem unitToPushforwardUnit_app_top_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (i : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ ⊤) (x : Γ(Y, ⊤)) :
    (Scheme.unitModule X).presheaf.map i.op
        ((Scheme.Modules.unitToPushforwardUnit f).app ⊤ x) = Scheme.Hom.appTop f x := by
  rw [Subsingleton.elim i (eqToHom (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)),
    show (Scheme.Modules.unitToPushforwardUnit f).app ⊤ x =
      (Scheme.Hom.toRingCatSheafHom f).hom.app (op ⊤) x from
    SheafOfModules.unitToPushforwardObjUnit_val_app_apply (Scheme.Hom.toRingCatSheafHom f) x]
  simp [Scheme.Hom.appTop, Scheme.Hom.app]
  rfl

/-- The comparison of iterated pullbacks carries `pullbackUnitIso` to `pullbackUnitIso`: for
`g : X ⟶ Y` over `S`, the identification `X^* 𝒪_S ≅ 𝒪_X` through `g^* Y^* 𝒪_S` is the pullback
along `g` of `Y^* 𝒪_S ≅ 𝒪_Y` followed by `g^* 𝒪_Y ≅ 𝒪_X`. -/
public theorem pullbackUnitIso_comp_app {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y) :
    ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule S)) ≫
        (Scheme.Modules.pullbackUnitIso X.hom).hom =
      (Scheme.Modules.pullback g.left).map (Scheme.Modules.pullbackUnitIso Y.hom).hom ≫
        (Scheme.Modules.pullbackUnitIso g.left).hom := by
  rw [← Scheme.Modules.pullbackUnitIso_comp_eq g.left Y.hom X.hom (Over.w g)]
  simp

/-- The morphism of modules whose value on `⊤` is the restriction map of the presheaf of
[Stacks, Tag 03DS] at `𝒪_S`, followed by the pushforward of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, is
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` preceded by `pullbackUnitIso`. -/
public theorem sectionMorphism_unit_comp_pullbackUnitIso {S : Scheme.{u}} {T U : Over S}
    (h : U ⟶ T) :
    ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app
          ((Scheme.Modules.pullback T.hom).obj (Scheme.unitModule S)) ≫
        (Scheme.Modules.pushforward h.left).map
          ((Scheme.Modules.pullbackComp h.left T.hom).hom.app (Scheme.unitModule S) ≫
            (Scheme.Modules.pullbackCongr (Over.w h)).hom.app (Scheme.unitModule S))) ≫
      (Scheme.Modules.pushforward h.left).map
        (Scheme.Modules.pullbackUnitIso U.hom).hom =
    (Scheme.Modules.pullbackUnitIso T.hom).hom ≫
      Scheme.Modules.unitToPushforwardUnit h.left := by
  rw [Category.assoc, ← Functor.map_comp, pullbackUnitIso_comp_app h,
    ← Scheme.Modules.pullbackUnitIso_homEquiv h.left,
    ← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]

/-- `AlgebraicGeometry.pullbackSectionsMap` written out: the unit of the pullback--pushforward
adjunction followed by the pushforward of the comparison of iterated pullbacks, read on `⊤` and
restricted. -/
public theorem pullbackSectionsMap_eq_app_top {S : Scheme.{u}} (F : S.Modules) {X Y : Over S}
    (g : X ⟶ Y) (i : (⊤ : X.left.Opens) ⟶ g.left ⁻¹ᵁ ⊤) :
    pullbackSectionsMap F g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback Y.hom).obj F) ≫
          (Scheme.Modules.pushforward g.left).map
            ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
              (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F)).app ⊤ ≫
        ((Scheme.Modules.pullback X.hom).obj F).presheaf.map i.op := by
  rw [Subsingleton.elim i (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp))]
  rfl

/-- Pulling a global section of `T^* 𝒪_S` back
along a morphism `h` of schemes over `S` and then identifying it with a global function is the
same as identifying first and then applying the ring map on global functions. -/
public theorem sectionsTop_pullbackUnitIso_naturality {S : Scheme.{u}} {T U : Over S} (h : U ⟶ T)
    (x : Γ((Scheme.Modules.pullback T.hom).obj (Scheme.unitModule S), ⊤)) :
    (Scheme.Modules.pullbackUnitIso U.hom).hom.app ⊤
        (pullbackSectionsMap (Scheme.unitModule S) h x) =
      Scheme.Hom.appTop h.left ((Scheme.Modules.pullbackUnitIso T.hom).hom.app ⊤ x) := by
  have hle : (⊤ : U.left.Opens) ≤ h.left ⁻¹ᵁ ⊤ := by simp
  rw [pullbackSectionsMap_eq_app_top (Scheme.unitModule S) h (homOfLE hle)]
  refine Eq.trans (Scheme.Modules.Hom.app_presheaf_map
    (Scheme.Modules.pullbackUnitIso U.hom).hom (homOfLE hle) _) ?_
  refine Eq.trans (congrArg ((Scheme.unitModule U.left).presheaf.map (homOfLE hle).op) ?_)
    (unitToPushforwardUnit_app_top_restrict h.left (homOfLE hle)
      ((Scheme.Modules.pullbackUnitIso T.hom).hom.app ⊤ x))
  exact congrArg (fun φ ↦ Scheme.Modules.Hom.app φ ⊤ x)
    (sectionMorphism_unit_comp_pullbackUnitIso h)

/-! ### `Gₐ = (𝒪_S)ᵃ` -/

/-- The presheaf of [Stacks, Tag 03DS] at the structure sheaf, `(f : T → S) ↦ Γ(T, f^* 𝒪_S)`, is
the presheaf of global functions `T ↦ Γ(T, 𝒪_T)` read additively. -/
public def quasiCoherentPresheafUnitIso (S : Scheme.{u}) :
    quasiCoherentPresheafFunctor S (Scheme.unitModule S) ≅ globalFunctionsAddPresheaf S :=
  NatIso.ofComponents
    (fun T ↦ (globalSectionsGroup (unop T).left).mapIso
      (Scheme.Modules.pullbackUnitIso (unop T).hom))
    (fun {_ _} g ↦ by
      ext x
      exact sectionsTop_pullbackUnitIso_naturality g.unop x)

/-- On any site of schemes over `S`, the abelian presheaf of [Stacks, Tag 03DU] attached to the
structure sheaf is the additive group presheaf of global functions, the presheaf underlying
`Gₐ`. -/
public def associatedPresheafUnitIso (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C]
    (toOver : C ⥤ Over S) :
    Stacks.Sites.associatedPresheaf S (Scheme.unitModule S) toOver ≅
      Stacks.Sites.additiveGroupPresheaf S toOver :=
  Functor.isoWhiskerLeft toOver.op (quasiCoherentPresheafUnitIso S)

/-! ### `Gₐ` on a localized big `τ`-site -/

variable (S : Scheme.{u}) (τ : CoveringTopology) (B : BigSite.{u} τ)
  (hS : S.size < cutoff τ B)

/-- Global functions are a sheaf of types on the localized big `τ`-site. -/
public theorem isSheaf_overGlobalSections :
    Presheaf.IsSheaf (overTopology τ B S hS)
      ((overToSlice τ B S hS).op ⋙ Stacks.Sites.globalSectionsOver S) :=
  (overToSlice τ B S hS).op_comp_isSheaf_of_isSheaf _ _ _
    (Stacks.Sites.isSheaf_fpqcOver_globalSections S)

/-- `Gₐ` on the localized big `τ`-site of `S`, uniform in `τ`: its sections over an object `T/S`
are the global functions `Γ(T, 𝒪_T)` under addition. -/
@[sga "3 I 4.3.1" "special case"]
public def overAdditiveGroupSheaf : Sheaf (overTopology τ B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S (overToSlice τ B S hS) (overTopology τ B S hS)
    (isSheaf_overGlobalSections S τ B hS)

/-- `Gₐ ≅ (𝒪_S)ᵃ` as abelian sheaves on the localized big `τ`-site. -/
public def overAdditiveGroupSheafIsoAssociatedSheaf :
    bigOverAssociatedSheaf S (Scheme.unitModule S) τ B hS ≅
      overAdditiveGroupSheaf S τ B hS :=
  (fullyFaithfulSheafToPresheaf (overTopology τ B S hS) AddCommGrpCat.{u}).preimageIso
    (associatedPresheafUnitIso S (overToSlice τ B S hS))

/-! #### The uniform `Gₐ` at the fppf, étale and Zariski sites -/

/-- At `τ = fppf` the uniform `Gₐ` is `AlgebraicGeometry.BigFppfOver.additiveGroupSheaf`. -/
public theorem overAdditiveGroupSheaf_fppf (B : BigFppfSite.{u}) (hB : B.Contains S) :
    overAdditiveGroupSheaf S .fppf B hB = BigFppfOver.additiveGroupSheaf S B hB := rfl

/-- At `τ = etale` the uniform `Gₐ` is `AlgebraicGeometry.BigEtaleOver.additiveGroupSheaf`. -/
public theorem overAdditiveGroupSheaf_etale (B : BigEtaleSite.{u}) (hB : B.Contains S) :
    overAdditiveGroupSheaf S .etale B hB = BigEtaleOver.additiveGroupSheaf S B hB := rfl

/-- At `τ = zariski` the uniform `Gₐ` is
`AlgebraicGeometry.BigZariskiOver.additiveGroupSheaf`. -/
public theorem overAdditiveGroupSheaf_zariski (B : BigZariskiSite.{u}) (hB : B.Contains S) :
    overAdditiveGroupSheaf S .zariski B hB = BigZariskiOver.additiveGroupSheaf S B hB := rfl

/-! ### The cohomology of `Gₐ` -/

/-- For a scheme `S` below the cutoff of a big `τ`-site and every `p`,
`H^p(X, 𝒪_X) ≅ H^p_τ(X, Gₐ)`: the left-hand side is the cohomology of the structure sheaf on the
underlying topological space of `S`, the right-hand side the `τ`-cohomology of `Gₐ` over the
final object `(opensBelowToOver hS).obj ⊤` of the localized big site. -/
@[stacks 03P6 "all degrees p ≥ 0: H^p_τ(X, Gₐ) = H^p(X, 𝒪_X), the specialization of \
Theorem 03P2 to ℱ = 𝒪_S.  τ is a bound variable, so this one declaration is the comparison for \
all five big sites at once, in particular for the fppf, étale and Zariski sites the remark \
names.  The left-hand side is cohomology of the structure sheaf on the site of opens of the \
underlying topological space of S, which is this repository's spelling of H^p(X, 𝒪_X), so the \
rightmost equality of the chain needs no further comparison.  The missing ingredient supplied \
here on top of 03P2 is Gₐ = (𝒪_S)ᵃ, namely \
overAdditiveGroupSheafIsoAssociatedSheaf",
  sga "1 XI 5.3" "G_a clause",
  sga "4 VII 4.2.1" "special case"]
public def additiveGroupSheafCohomologyIso (p : ℕ) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj (Scheme.unitModule S)) p ⊤ ≅
      Sheaf.H' (overAdditiveGroupSheaf S τ B hS) p
        ((opensBelowToOver (κ := cutoff τ B) hS).obj ⊤) :=
  bigOverQuasiCoherentGlobalCohomologyIso S (Scheme.unitModule S) τ B hS p ≪≫
    ((Sheaf.cohomologyPresheafFunctor (overTopology τ B S hS) p).mapIso
      (overAdditiveGroupSheafIsoAssociatedSheaf S τ B hS)).app
      (op ((opensBelowToOver (κ := cutoff τ B) hS).obj ⊤))

variable (Be : BigEtaleSite.{u}) (hSe : Be.Contains S)
  (Bz : BigZariskiSite.{u}) (hSz : Bz.Contains S)
  (Bf : BigFppfSite.{u}) (hSf : Bf.Contains S)

/-- `H^p_{fppf}(X, Gₐ) ≅ H^p_{étale}(X, Gₐ)` for every `p`, both being `H^p(X, 𝒪_X)`. -/
@[stacks 03P6 "all degrees p ≥ 0: H^p_fppf(X, Gₐ) = H^p_étale(X, Gₐ), the first leg of the \
chain, obtained by composing additiveGroupSheafCohomologyIso at τ = fppf with its inverse at \
τ = étale.  The sheaves are BigFppfOver.additiveGroupSheaf and BigEtaleOver.additiveGroupSheaf \
themselves, by overAdditiveGroupSheaf_fppf and overAdditiveGroupSheaf_etale.  The degree-zero \
case is additiveGroupSheafHZeroFppfEtaleAddEquiv"]
public def additiveGroupSheafCohomologyFppfEtaleIso (p : ℕ) :
    Sheaf.H' (BigFppfOver.additiveGroupSheaf S Bf hSf) p
        ((opensBelowToOver (κ := cutoff .fppf Bf) hSf).obj ⊤) ≅
      Sheaf.H' (BigEtaleOver.additiveGroupSheaf S Be hSe) p
        ((opensBelowToOver (κ := cutoff .etale Be) hSe).obj ⊤) :=
  (additiveGroupSheafCohomologyIso S .fppf Bf hSf p).symm ≪≫
    additiveGroupSheafCohomologyIso S .etale Be hSe p

/-- `H^p_{fppf}(X, Gₐ) ≅ H^p_{Zar}(X, Gₐ)` for every `p`, both being `H^p(X, 𝒪_X)`. -/
@[stacks 03P6 "all degrees p ≥ 0: H^p_fppf(X, Gₐ) = H^p_Zar(X, Gₐ), the second leg of the \
chain.  With additiveGroupSheafCohomologyFppfEtaleIso and additiveGroupSheafCohomologyIso this \
completes the chain H^p_fppf = H^p_étale = H^p_Zar = H^p(X, 𝒪_X) for all p ≥ 0.  The sheaves \
are BigFppfOver.additiveGroupSheaf and BigZariskiOver.additiveGroupSheaf themselves, by \
overAdditiveGroupSheaf_fppf and overAdditiveGroupSheaf_zariski.  The degree-zero case is \
additiveGroupSheafHZeroFppfZariskiAddEquiv"]
public def additiveGroupSheafCohomologyFppfZariskiIso (p : ℕ) :
    Sheaf.H' (BigFppfOver.additiveGroupSheaf S Bf hSf) p
        ((opensBelowToOver (κ := cutoff .fppf Bf) hSf).obj ⊤) ≅
      Sheaf.H' (BigZariskiOver.additiveGroupSheaf S Bz hSz) p
        ((opensBelowToOver (κ := cutoff .zariski Bz) hSz).obj ⊤) :=
  (additiveGroupSheafCohomologyIso S .fppf Bf hSf p).symm ≪≫
    additiveGroupSheafCohomologyIso S .zariski Bz hSz p

end AlgebraicGeometry

end
