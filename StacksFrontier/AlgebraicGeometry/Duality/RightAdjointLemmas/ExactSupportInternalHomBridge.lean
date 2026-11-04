module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTraceSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSource

/-!
# The two spellings of the internal Hom from `i_* 𝒪_Z`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces.  The sheaf
`ℰom_{𝒪_X}(i_* 𝒪_Z, F)` occurs in the tree under two names, with the same sections over every
open — the morphisms `(i_* 𝒪_Z)|_U ⟶ F|_U` on the slice site over `U` — but with two different
`𝒪_X`-module structures:

* `…homSheafFromPushforwardStructureSheaf`, the internal Hom of [Stacks, Tag 0932] from the
  ring sheaf `i_* 𝒪_Z` along the comorphism `𝒪_X ⟶ i_* 𝒪_Z`, with its scalar action by *right
  multiplication in `i_* 𝒪_Z` on the source*, restricted to `𝒪_X`;  this is the model in which
  the adjunction of [Stacks, Tag 0A75] and its counit are available
  (`…modulePushforwardSheafHomExactSupportIsoHomSheaf`, `…evaluationAtOne`);
* `AlgebraicGeometry.RingedSite.internalHomSheaf`, the internal Hom of [Stacks, Tag 03EM] of two
  sheaves of modules, with its scalar action by *multiplication on the target*;  this is the
  model the internal Hom complex of [Stacks, Tag 0A8Z] is assembled from.

The two agree, the identity on sections being an isomorphism of `𝒪_X`-modules, because a
morphism out of `(i_* 𝒪_Z)|_U` is `𝒪_X`-linear and `i_* 𝒪_Z` is commutative.  That is the only
content of this file, and it is what lets the counit of [Stacks, Tag 0A75] be read inside the
internal Hom complex.

## Main definitions

* `…homSheafFromPushforwardStructureSheafIsoInternalHom`: the isomorphism of functors
  `ℰom_{𝒪_X}(i_* 𝒪_Z, -) ≅ ℰom_{𝒪_X}(i_* 𝒪_Z, -)` between the two spellings.

## Main results

* `…homSheafFromPushforwardStructureSheafIsoInternalHom_hom_val_app`: the isomorphism is the
  identity on sections, which is what pins it down.

## Implementation notes

The scalar actions differ: on the first spelling `r • ψ` is `ψ` precomposed with right
multiplication by the image of `r` in `i_* 𝒪_Z`, on the second it is `ψ` postcomposed with
multiplication by `r` on the target.  They agree because, over an object `V` of the slice site,
`ψ` is linear over the sections of `𝒪_X` there and the image of `r` is central: both sides send
a section `x` of `i_* 𝒪_Z` to `r · ψ(x)`.  Commutativity of `i_* 𝒪_Z` is read off from the
commutativity of `𝒪_Z` on the preimage open, and is isolated as `…mul_comm_pushed` so that no
step below has to look through the pushforward for a `CommRing` instance.

The section-level statements are phrased with the elements and the scalars in the spelling the
elaborator produces from the goal, rather than in a uniform one: the two module structures are
definitionally equal but their rings are reached by different unfoldings, so instance search for
`HSMul` fails on a mixed spelling even where the defeq check succeeds.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The ambient ringed space `X`, read as a ringed site. -/
abbrev ringedSiteX : RingedSite.{u, u, u} := Stacks.SheafOfModules.ringedSite S.X.sheaf

/-- `i_* 𝒪_Z`, as a sheaf of `𝒪_X`-modules. -/
abbrev pushforwardStructureModule : SheafOfModules.{u} (structureSheafRing S.X) :=
  (modulePushforward S.i).obj (SheafOfModules.unit (structureSheafRing S.Z))

/-- The `𝒪_X(U)`-module structure on the sections of the internal Hom sheaf of [Stacks,
Tag 03EM], at the spelling in which instance search does not find it. -/
local instance moduleInternalHomSections
    (A G : SheafOfModules.{u} (structureSheafRing S.X)) (U : (Opens S.X)ᵒᵖ) :
    Module ((structureSheafRing S.X).obj.obj U)
      ((AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S) A G).val.obj U : Type u) :=
  homModule (ringedSiteX S).O.obj (AlgebraicGeometry.RingedSite.valOf (ringedSiteX S) A)
    (AlgebraicGeometry.RingedSite.valOf (ringedSiteX S) G) U.unop

/-- **Commutativity of the sections of `i_* 𝒪_Z`**, in the form the comparison below consumes:
the two factors may be swapped, and one of them replaced by an equal section.  The sections of
`i_* 𝒪_Z` over `W` are the sections of `𝒪_Z` over the preimage of `W`, where commutativity is
available. -/
theorem mul_comm_pushed (W : Opens S.X)
    (a b c : (S.Z.presheaf.obj (op ((opensMap S.i).obj W)) : Type u)) (h : b = c) :
    a * b = c * a := by
  subst h
  exact mul_comm a b

variable (F : SheafOfModules.{u} (structureSheafRing S.X))

/-- **The identity on sections is `𝒪_X(U)`-linear for the two module structures on
`ℰom_{𝒪_X}(i_* 𝒪_Z, F)(U)`.**  Acting by `r` on the source, by right multiplication by the
image of `r` in `i_* 𝒪_Z`, is acting by `r` on the target, because a local morphism out of
`i_* 𝒪_Z` is `𝒪_X`-linear and `i_* 𝒪_Z` is commutative. -/
def internalHomSectionsComparison (U : (Opens S.X)ᵒᵖ) :
    (S.homSheafFromPushforwardStructureSheaf.obj F).val.obj U ⟶
      (AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
        (pushforwardStructureModule S) F).val.obj U :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun := fun ψ => ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun r ψ => by
        have hL : ∀ (V : (Over U.unop)ᵒᵖ) (y : _),
            (ModuleCat.Hom.hom ((r • ψ).app V)) y =
              (ModuleCat.Hom.hom (ψ.app V))
                (Stacks.PresheafOfModules.CoextendScalars.rightMulComp
                  (structureSheafHom S.i).hom U.unop
                  (((structureSheafHom S.i).hom.app U) r) V y) := fun _ _ => rfl
        refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        refine Eq.trans (hL V x) (Eq.trans (congrArg (ModuleCat.Hom.hom (ψ.app V)) ?_)
          ((ModuleCat.Hom.hom (ψ.app V)).map_smul
            (fRestr (ringedSiteX S).O.obj U.unop r V) x))
        have hnat := ConcreteCategory.congr_hom
          ((structureSheafHom S.i).hom.naturality V.unop.hom.op) r
        simp only [CategoryTheory.comp_apply] at hnat
        refine Eq.trans (Stacks.PresheafOfModules.CoextendScalars.rightMulComp_apply
          (structureSheafHom S.i).hom U.unop (((structureSheafHom S.i).hom.app U) r) V x) ?_
        have hnat2 : (S.pushedRingSheaf.obj.map V.unop.hom.op)
              (((structureSheafHom S.i).hom.app U) r) =
            ((structureSheafHom S.i).hom.app (op V.unop.left))
              (((structureSheafRing S.X).obj.map V.unop.hom.op) r) := hnat.symm
        exact mul_comm_pushed S V.unop.left x _ _ hnat2 }

/-- The comparison of the two spellings is the identity on sections. -/
theorem internalHomSectionsComparison_apply (U : (Opens S.X)ᵒᵖ)
    (ψ : (S.homSheafFromPushforwardStructureSheaf.obj F).val.obj U) :
    (ModuleCat.Hom.hom (internalHomSectionsComparison S F U)) ψ = ψ := rfl

/-- **The two spellings of `ℰom_{𝒪_X}(i_* 𝒪_Z, F)` agree**, by the identity on sections. -/
def internalHomComparisonVal :
    (S.homSheafFromPushforwardStructureSheaf.obj F).val ⟶
      (AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
        (pushforwardStructureModule S) F).val where
  app U := internalHomSectionsComparison S F U
  naturality {U V} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun ψ => ?_)
    refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    refine Eq.trans (Stacks.PresheafOfModules.CoextendScalars.coextRestrFun_app_apply
      (structureSheafHom S.i).hom F.val f ψ W.unop.hom (W.unop.hom ≫ f.unop) rfl a) ?_
    exact (Stacks.PresheafOfModules.InternalHom.internalHom_map_app_apply
      (ringedSiteX S).O.obj (AlgebraicGeometry.RingedSite.valOf (ringedSiteX S)
        (pushforwardStructureModule S))
      (AlgebraicGeometry.RingedSite.valOf (ringedSiteX S) F) f.unop ψ W.unop a).symm

/-- **The two spellings of `ℰom_{𝒪_X}(i_* 𝒪_Z, F)` agree**, as sheaves of `𝒪_X`-modules. -/
def internalHomComparison :
    S.homSheafFromPushforwardStructureSheaf.obj F ⟶
      AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
        (pushforwardStructureModule S) F :=
  ⟨internalHomComparisonVal S F⟩

/-- The comparison is invertible on sections over every open: it is the identity map. -/
instance isIso_internalHomSectionsComparison (U : (Opens S.X)ᵒᵖ) :
    IsIso (internalHomSectionsComparison S F U) :=
  inferInstanceAs (IsIso (LinearEquiv.ofBijective
    (ModuleCat.Hom.hom (internalHomSectionsComparison S F U))
    Function.bijective_id).toModuleIso.hom)

/-- **The comparison of the two spellings is an isomorphism.** -/
instance isIso_internalHomComparison : IsIso (internalHomComparison S F) := by
  have ha : (PresheafOfModules.isoMk
        (fun U => asIso (internalHomSectionsComparison S F U))
        (fun {_ _} g => (internalHomComparisonVal S F).naturality g)).hom =
      (internalHomComparison S F).val :=
    PresheafOfModules.hom_ext fun _ => rfl
  have hval : IsIso (internalHomComparison S F).val := by
    rw [← ha]
    infer_instance
  have : IsIso ((SheafOfModules.forget (structureSheafRing S.X)).map
    (internalHomComparison S F)) := hval
  exact isIso_of_reflects_iso (internalHomComparison S F)
    (SheafOfModules.forget (structureSheafRing S.X))

/-- **The two spellings of `ℰom_{𝒪_X}(i_* 𝒪_Z, F)`, identified.** -/
def internalHomComparisonIso :
    S.homSheafFromPushforwardStructureSheaf.obj F ≅
      AlgebraicGeometry.RingedSite.internalHomSheaf (ringedSiteX S)
        (pushforwardStructureModule S) F :=
  asIso (internalHomComparison S F)

/-- The comparison of the two spellings is natural in the target module: both spellings act on
a morphism of the target by postcomposition. -/
theorem internalHomComparison_naturality {F G : SheafOfModules.{u} (structureSheafRing S.X)}
    (g : F ⟶ G) :
    S.homSheafFromPushforwardStructureSheaf.map g ≫ internalHomComparison S G =
      internalHomComparison S F ≫
        AlgebraicGeometry.RingedSite.internalHomPost (ringedSiteX S) g := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ψ => ?_))
  rfl

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
