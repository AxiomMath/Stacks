module

public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianPushforwardExact
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pushforward along a closed embedding commutes with extension by zero

Let `f : (Z, 𝒪_Z) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces whose underlying continuous map is
a closed embedding, let `U ⊆ X` be open and let `V = f⁻¹U`. For a sheaf of `𝒪_Z`-modules `M`,
cutting `M` down to `V` and extending by zero commutes with `f_*`:

`f_*(j_{V,!} j_V^* M) ≅ j_{U,!} j_U^* (f_* M)`,

naturally in `M`. Both sides have stalk `M_z` at a point `f z` with `z ∈ V`, and vanishing stalk
everywhere else.

## Main results

* `ExtensionByZeroModules.modulePushforwardExtensionRestrictionIso`: the isomorphism of functors
  `j_{V,!} j_V^* ⋙ f_* ≅ f_* ⋙ j_{U,!} j_U^*`.
* `ExtensionByZeroModules.isZero_stalk_modulePushforward_jShriek`: the stalks of
  `f_*(j_{V,!} N)` vanish off `U`.

## Implementation notes

No map is written down by hand. Both functors receive a transformation from
`j_{V,!} j_V^* ⋙ f_* ⋙ j_{U,!} j_U^*`: the counit of `j_{U,!} ⊣ j_U^*`, and
`j_{U,!} j_U^* f_*` of the counit of `j_{V,!} ⊣ j_V^*`. The first is invertible by Stacks 00AB,
the stalks of `f_*(j_{V,!} j_V^* M)` vanishing off `U`; the second because the stalks of `f_*` of
the counit are invertible at the points of `U`. Both stalk computations use that the stalk of
`f_* G` at `f z` is the stalk of `G` at `z`, `f` being inducing, and that the stalk of `f_* G`
off the image of `f` vanishes, the image being closed (Stacks 00AE).

## References

* [Stacks Project, Lemma 17.6.1 (Tag 00AB)](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Lemma 6.31.4 (Tag 00AE)](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.ExtensionByZeroBaseChange

universe u

namespace ExtensionByZeroModules

variable {Z X : RingedSpace.{u, u}} (f : Z ⟶ X)
  (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))

include hf

/-- The stalk of `f_* G` at `f z` is the stalk of `G` at `z`, `f` being inducing. -/
theorem isIso_stalkPushforward_modulePushforward (G : SheafOfModules.{u} (structureSheafRing Z))
    (z : Z.carrier) :
    IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      ((toAb (structureSheafRing Z)).obj G) z) :=
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
    hf.isInducing _ z

/-- The stalk of `f_* G` vanishes off the image of `f` (Stacks 00AE). -/
theorem isZero_stalk_modulePushforward_of_notMem_range
    (G : SheafOfModules.{u} (structureSheafRing Z)) (x : X.carrier)
    (hx : x ∉ Set.range (ConcreteCategory.hom f.hom.base)) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((toAb (structureSheafRing X)).obj ((modulePushforward f).obj G))) :=
  IsZero.of_iso (isZero_zero AddCommGrpCat.{u})
    ((ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange f.hom.base G.isSheaf hf x
      hx).uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- `f_*` of a morphism invertible on the stalks over a point `x` is invertible on the stalk at
`x`. -/
theorem isIso_stalk_modulePushforward_map {M N : SheafOfModules.{u} (structureSheafRing Z)}
    (φ : M ⟶ N) (x : X.carrier)
    (h : ∀ z : Z.carrier, f.hom.base z = x →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((toAb (structureSheafRing Z)).map φ))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toAb (structureSheafRing X)).map ((modulePushforward f).map φ))) := by
  by_cases hx : x ∈ Set.range (ConcreteCategory.hom f.hom.base)
  · obtain ⟨z, rfl⟩ := hx
    have hM := isIso_stalkPushforward_modulePushforward f hf M z
    have hN := isIso_stalkPushforward_modulePushforward f hf N z
    have hsq := TopCat.Presheaf.stalkPushforward_naturality f.hom.base
      ((toAb (structureSheafRing Z)).map φ) z
    have hc := @IsIso.comp_isIso _ _ _ _ _ _ _ hM (h z rfl)
    rw [hsq] at hc
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hN hc
  · exact (isZero_stalk_modulePushforward_of_notMem_range f hf M x hx).isIso
      (isZero_stalk_modulePushforward_of_notMem_range f hf N x hx) _

variable (U : Opens X.carrier) (V : Opens Z.carrier)
  (hUV : (Opens.map f.hom.base).obj U = V)

include hUV

/-- **The stalks of `f_*(j_{V,!} N)` vanish off `U`.** Off the image of `f` this is Stacks 00AE;
at `f z` with `f z ∉ U` the stalk is that of `j_{V,!} N` at `z ∉ V`, which vanishes by
Stacks 00AB. -/
theorem isZero_stalk_modulePushforward_jShriek
    (N : SheafOfModules.{u} (resRing V (structureSheafRing Z))) (x : X.carrier) (hx : x ∉ U) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((toAb (structureSheafRing X)).obj
        ((modulePushforward f).obj ((jShriek V (structureSheafRing Z)).obj N)))) := by
  by_cases hr : x ∈ Set.range (ConcreteCategory.hom f.hom.base)
  · obtain ⟨z, rfl⟩ := hr
    have hz : z ∉ V := fun hz => hx (by rw [← hUV] at hz; exact hz)
    exact (isZero_stalk_jShriek V (structureSheafRing Z) N z hz).of_iso
      (@asIso _ _ _ _ _ (isIso_stalkPushforward_modulePushforward f hf
        ((jShriek V (structureSheafRing Z)).obj N) z))
  · exact isZero_stalk_modulePushforward_of_notMem_range f hf _ x hr

/-- The counit of `j_{U,!} ⊣ j_U^*` at `f_*(j_{V,!} j_V^* M)`, as a transformation of functors of
`M`. It is invertible, `f_*(j_{V,!} j_V^* M)` having vanishing stalks off `U`. -/
def modulePushforwardExtensionRestrictionCounit :
    (jStar V (structureSheafRing Z) ⋙ jShriek V (structureSheafRing Z) ⋙ modulePushforward f) ⋙
        jStar U (structureSheafRing X) ⋙ jShriek U (structureSheafRing X) ⟶
      jStar V (structureSheafRing Z) ⋙ jShriek V (structureSheafRing Z) ⋙ modulePushforward f :=
  Functor.whiskerLeft _ (jShriekAdjunction U (structureSheafRing X)).counit

/-- `j_{U,!} j_U^* f_*` of the counit of `j_{V,!} ⊣ j_V^*`, as a transformation of functors. It
is invertible, `f_*` of that counit being invertible on the stalks at the points of `U`. -/
def extensionRestrictionModulePushforwardCounit :
    (jStar V (structureSheafRing Z) ⋙ jShriek V (structureSheafRing Z)) ⋙
        modulePushforward f ⋙ jStar U (structureSheafRing X) ⋙ jShriek U (structureSheafRing X) ⟶
      𝟭 _ ⋙ modulePushforward f ⋙ jStar U (structureSheafRing X) ⋙
        jShriek U (structureSheafRing X) :=
  Functor.whiskerRight (jShriekAdjunction V (structureSheafRing Z)).counit _

/-- The counit of `j_{U,!} ⊣ j_U^*` at `f_*(j_{V,!} j_V^* M)` is invertible. -/
theorem isIso_modulePushforwardExtensionRestrictionCounit :
    IsIso (modulePushforwardExtensionRestrictionCounit f U V) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => ?_
  exact counit_isIso_of_stalk_isZero U (structureSheafRing X) _
    fun x hx => isZero_stalk_modulePushforward_jShriek f hf U V hUV _ x hx

/-- `j_{U,!} j_U^* f_*` of the counit of `j_{V,!} ⊣ j_V^*` is invertible. -/
theorem isIso_extensionRestrictionModulePushforwardCounit :
    IsIso (extensionRestrictionModulePushforwardCounit f U V) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => ?_
  have h : IsIso ((jStar U (structureSheafRing X)).map ((modulePushforward f).map
      ((jShriekAdjunction V (structureSheafRing Z)).counit.app M))) := by
    refine isIso_jStar_map_of_stalk_isIso (structureSheafRing X) U _ fun x hx => ?_
    refine isIso_stalk_modulePushforward_map f hf _ x fun z hz => ?_
    subst hz
    exact isIso_stalk_of_isIso_jStar_map (structureSheafRing Z) V _
      (isIso_jStar_map_counit (structureSheafRing Z) V M) z (by rw [← hUV]; exact hx)
  exact Functor.map_isIso (jShriek U (structureSheafRing X)) _

/-- **Pushforward along a closed embedding commutes with extension by zero.** For a morphism of
ringed spaces `f : Z ⟶ X` whose underlying map is a closed embedding, an open `U ⊆ X` and
`V = f⁻¹U`, there is a natural isomorphism `f_*(j_{V,!} j_V^* M) ≅ j_{U,!} j_U^* (f_* M)`. -/
def modulePushforwardExtensionRestrictionIso :
    jStar V (structureSheafRing Z) ⋙ jShriek V (structureSheafRing Z) ⋙ modulePushforward f ≅
      modulePushforward f ⋙ jStar U (structureSheafRing X) ⋙ jShriek U (structureSheafRing X) :=
  have := isIso_modulePushforwardExtensionRestrictionCounit f hf U V hUV
  have := isIso_extensionRestrictionModulePushforwardCounit f hf U V hUV
  (asIso (modulePushforwardExtensionRestrictionCounit f U V)).symm ≪≫
    asIso (extensionRestrictionModulePushforwardCounit f U V)

end ExtensionByZeroModules

