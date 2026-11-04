module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveSheafify

/-!
# Sections of the constant sheaf of modules on the small étale site of a scheme

Let `X` be a scheme, `R` a ring and `M` an `R`-module. The constant sheaf of `R`-modules with
value `M` on the small étale site `X.Etale` has as its sections over an étale `X`-scheme `V` the
module of Zariski locally constant `M`-valued maps on `V`. This is the module form of
`AlgebraicGeometry.smallEtaleConstantSheafIsoLocallyConstantMapsAb`.

## Main definitions

* `AlgebraicGeometry.locallyConstantMapsModule` — the presheaf of `R`-modules on schemes sending
  a scheme to the module of locally constant `M`-valued maps on it.
* `AlgebraicGeometry.smallEtaleLocallyConstantMapsModule` — its restriction to the small étale
  site of a scheme, and `AlgebraicGeometry.smallEtaleLocallyConstantMapsModuleSheaf` the sheaf.
* `AlgebraicGeometry.constantToSmallEtaleLocallyConstantMapsModule` — the map of presheaves of
  modules sending `m : M` to the constant map with value `m`.
* `AlgebraicGeometry.constantSheafToSmallEtaleLocallyConstantMapsModule` — the comparison from
  the constant sheaf of modules, and `smallEtaleConstantSheafIsoLocallyConstantMapsModule` the
  resulting identification.

## Main results

* `AlgebraicGeometry.isIso_constantSheafToSmallEtaleLocallyConstantMapsModule` — the comparison
  is an isomorphism.
* `AlgebraicGeometry.constantSheafToSmallEtaleLocallyConstantMapsModule_unit` fixes it by its
  action on constant sections.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w r

namespace AlgebraicGeometry

variable (R : Type r) [Ring R]

/-- The presheaf of `R`-modules on schemes sending a scheme to the module of locally constant
`M`-valued maps on it, with pullback of functions on morphisms. -/
public def locallyConstantMapsModule (M : Type w) [AddCommGroup M] [Module R M] :
    Scheme.{u}ᵒᵖ ⥤ ModuleCat.{max u w} R where
  obj T := ModuleCat.of R (LocallyConstant T.unop M)
  map f := ModuleCat.ofHom (LocallyConstant.comapₗ R f.unop.base.hom)
  map_id T := by
    ext f x
    rfl
  map_comp f g := by
    ext h x
    rfl

/-- The presheaf of `R`-modules on the small étale site of `X` sending an étale `X`-scheme `V` to
the module of locally constant `M`-valued maps on `V`. -/
public abbrev smallEtaleLocallyConstantMapsModule (X : Scheme.{u}) (M : Type w) [AddCommGroup M]
    [Module R M] : (X.Etale)ᵒᵖ ⥤ ModuleCat.{max u w} R :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ locallyConstantMapsModule.{u, w} R M

/-- The underlying presheaf of abelian groups of the presheaf of locally constant maps of modules
is the presheaf of locally constant maps of abelian groups. -/
public def smallEtaleLocallyConstantMapsModuleForget₂Iso (X : Scheme.{u}) (M : Type w)
    [AddCommGroup M] [Module R M] :
    smallEtaleLocallyConstantMapsModule.{u, w} R X M ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      smallEtaleLocallyConstantMapsAb.{u, w} X M :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Locally constant `M`-valued maps form a sheaf of `R`-modules on the small étale site. -/
public theorem smallEtaleLocallyConstantMapsModule_isSheaf (X : Scheme.{u})
    (M : Type (max (u + 1) v)) [AddCommGroup M] [Module R M] :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X)
      (smallEtaleLocallyConstantMapsModule.{u, max (u + 1) v} R X M) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ (ModuleCat R) AddCommGrpCat) <|
    (Presheaf.isSheaf_of_iso_iff
      (smallEtaleLocallyConstantMapsModuleForget₂Iso.{u, max (u + 1) v} R X M)).mpr
    (smallEtaleLocallyConstantMapsAb_isSheaf.{u, v} X M)

/-- Locally constant `M`-valued maps, as a sheaf of `R`-modules on the small étale site. -/
public abbrev smallEtaleLocallyConstantMapsModuleSheaf (X : Scheme.{u})
    (M : Type (max (u + 1) v)) [AddCommGroup M] [Module R M] :
    Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) v} R) :=
  ⟨_, smallEtaleLocallyConstantMapsModule_isSheaf.{u, v} R X M⟩

/-- The map of presheaves of `R`-modules on the small étale site of `X` sending `m : M` to the
constant map with value `m`. -/
public def constantToSmallEtaleLocallyConstantMapsModule (X : Scheme.{u})
    (M : ModuleCat.{max (u + 1) v} R) :
    (Functor.const (X.Etale)ᵒᵖ).obj M ⟶
      smallEtaleLocallyConstantMapsModule.{u, max (u + 1) v} R X M where
  app T := ModuleCat.ofHom (LocallyConstant.constₗ R (X := T.unop.left))
  naturality T₁ T₂ f := by
    ext a
    rfl

/-- The comparison from the constant presheaf of modules to the presheaf of locally constant maps
is locally injective. -/
public theorem constantToSmallEtaleLocallyConstantMapsModule_isLocallyInjective
    (X : Scheme.{u}) (M : ModuleCat.{max (u + 1) v} R) :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X)
      (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M) := by
  classical
  refine ⟨fun {T} a b hab => ?_⟩
  change LocallyConstant.const T.unop.left a = LocallyConstant.const T.unop.left b at hab
  by_cases hab' : a = b
  · subst b
    simp
  · have hEmpty : IsEmpty T.unop.left := ⟨fun x => hab' <| by
      simpa using congrArg (fun f : LocallyConstant T.unop.left M => f x) hab⟩
    have heq : Presheaf.equalizerSieve
        (F := (Functor.const (X.Etale)ᵒᵖ).obj M) (X := T) a b = ⊥ := by
      ext V f
      simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
      exact ⟨fun hf => (hab' (by simpa using hf)).elim, False.elim⟩
    rw [heq]
    exact smallEtale_bot_mem X hEmpty

/-- The comparison from the constant presheaf of modules to the presheaf of locally constant maps
is locally surjective. -/
public theorem constantToSmallEtaleLocallyConstantMapsModule_isLocallySurjective
    (X : Scheme.{u}) (M : ModuleCat.{max (u + 1) v} R) :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M) := by
  classical
  refine ⟨fun {T} s => ?_⟩
  let s₀ : LocallyConstant T.left M := s
  choose O hO hx hconst using s₀.isLocallyConstant.exists_open
  let U : T.left → T.left.Opens := fun x => ⟨O x, hO x⟩
  have hU : TopologicalSpace.IsOpenCover U :=
    top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtaleScheme_openCoverData X U hU
  refine (Scheme.smallEtaleTopology X).superset_covering (fun V f hf => ?_) hcover
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
  refine (Presheaf.imageSieve
    (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M) s).downward_closed ?_ g
  refine ⟨s₀ (r i), ?_⟩
  show LocallyConstant.const (W i).left (s₀ (r i)) =
    LocallyConstant.comapₗ R
      ((Scheme.Etale.forget X ⋙ Over.forget X).map (a i)).base.hom s₀
  refine LocallyConstant.ext fun y => ?_
  show s₀ (r i) = s₀ ((Scheme.Etale.forget X ⋙ Over.forget X).map (a i) y)
  exact (hconst (r i) _ (hmaps i y)).symm

/-- The comparison from the constant sheaf of modules to the sheaf of locally constant maps: the
map out of the sheafification induced by
`AlgebraicGeometry.constantToSmallEtaleLocallyConstantMapsModule`. -/
public def constantSheafToSmallEtaleLocallyConstantMapsModule (X : Scheme.{u})
    (M : ModuleCat.{max (u + 1) v} R) :
    (constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) v} R)).obj M ⟶
      smallEtaleLocallyConstantMapsModuleSheaf.{u, v} R X M :=
  ⟨sheafifyLift (Scheme.smallEtaleTopology X)
    (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M)
    (smallEtaleLocallyConstantMapsModule_isSheaf.{u, v} R X M)⟩

/-- The comparison from the constant sheaf of `R`-modules with value `M` on the small étale site
of a scheme `X` to the sheaf of locally constant `M`-valued maps is an isomorphism. -/
public instance isIso_constantSheafToSmallEtaleLocallyConstantMapsModule (X : Scheme.{u})
    (M : ModuleCat.{max (u + 1) v} R) :
    IsIso (constantSheafToSmallEtaleLocallyConstantMapsModule.{u, v} R X M) := by
  have : (Scheme.smallEtaleTopology X).WEqualsLocallyBijective (ModuleCat.{max (u + 1) v} R) :=
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, max (u + 1) v} _ R
  exact Presheaf.isIso_of_toSheafify_comp_eq_of_isLocallyBijective _
    (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M) _
    (toSheafify_sheafifyLift _ _ _)
    (constantToSmallEtaleLocallyConstantMapsModule_isLocallyInjective.{u, v} R X M)
    (constantToSmallEtaleLocallyConstantMapsModule_isLocallySurjective.{u, v} R X M)

/-- The identification of the constant sheaf of modules on the small étale site with the sheaf of
locally constant maps. -/
public abbrev smallEtaleConstantSheafIsoLocallyConstantMapsModule (X : Scheme.{u})
    (M : ModuleCat.{max (u + 1) v} R) :
    (constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{max (u + 1) v} R)).obj M ≅
      smallEtaleLocallyConstantMapsModuleSheaf.{u, v} R X M :=
  asIso (constantSheafToSmallEtaleLocallyConstantMapsModule.{u, v} R X M)

/-- The comparison from the constant sheaf of modules to the locally constant maps sends the
sheafification-unit image of `m : M` to the constant map with value `m`. -/
public theorem constantSheafToSmallEtaleLocallyConstantMapsModule_unit (X : Scheme.{u})
    (M : ModuleCat.{max (u + 1) v} R) (T : (X.Etale)ᵒᵖ) (m : M) :
    ((constantSheafToSmallEtaleLocallyConstantMapsModule.{u, v} R X M).hom.app T)
      ((toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const (X.Etale)ᵒᵖ).obj M)).app T m) =
      (LocallyConstant.const T.unop.left m : LocallyConstant T.unop.left M) :=
  congrArg (fun f ↦ (f.app T).hom m) (toSheafify_sheafifyLift (Scheme.smallEtaleTopology X)
    (constantToSmallEtaleLocallyConstantMapsModule.{u, v} R X M)
    (smallEtaleLocallyConstantMapsModule_isSheaf.{u, v} R X M))

end AlgebraicGeometry

end
