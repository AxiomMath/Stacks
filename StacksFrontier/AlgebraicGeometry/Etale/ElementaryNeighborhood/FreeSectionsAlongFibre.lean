module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.LinearAlgebra.StdBasis
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessAlongFibre
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFiniteType
public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFromFiniteTypeFlatness
public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Free global sections on an affine étale cover of a flat fibre

Stacks Tag 05L0 says: for `f : X ⟶ S` of finite presentation, `F` a quasi-coherent `𝒪_X`-module
of finite type and `s : S` such that `F` is flat over `S` at every point of the fibre `X_s`, there
are an elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a commutative diagram
```
  X  ←ᵍ  X'
  ↓      ↓
  S  ←  Spec 𝒪_{S', s'}
```
in which `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `X_s = g((X')_{s'})`, `X'` is affine and of
finite presentation over `𝒪_{S', s'}`, `g^*F` is of finite presentation, and `Γ(X', g^*F)` is a
*free* `𝒪_{S', s'}`-module.

The proof is the source's. Tag 05KY gives, at each point `x` of the fibre, an elementary étale
neighbourhood `(S_x, s_x)` and an affine chart `Y_x ⟶ X ×_S Spec 𝒪_{S_x, s_x}` which is étale,
hits `x`, and has free sections. Because `Y_x ⟶ X ×_S Spec 𝒪_{S_x, s_x}` is étale and
`(S_x, s_x)` is elementary, the fibre of that pullback over the closed point is `X_s` itself, so
the image of `(Y_x)_{s_x}` is an open neighbourhood of `x` in `X_s`; the fibre being quasi-compact,
finitely many of these cover it. Tag 057B makes the elementary étale neighbourhoods of `(S, s)`
cofiltered, so one neighbourhood `(S', s')` dominates the finitely many chosen ones, and
`X' = ∐ Y_{x_i} ×_{Spec 𝒪_{S_{x_i}, s_{x_i}}} Spec 𝒪_{S', s'}` is the required cover: its
sections are the product of the base changes of the sections of the `Y_{x_i}`, each of which is
free because freeness survives base change of quasi-coherent modules along an affine morphism
(Tag 02KG), and a finite product of free modules is free.

## Main definitions

* `AlgebraicGeometry.specBaseScalars` is the ring map `R ⟶ Γ(Z, ⊤)` induced by a morphism
  `Z ⟶ Spec R`, and `AlgebraicGeometry.globalSectionsModuleOfSpecBase` is the restriction of
  scalars along it of the global sections of a module on `Z`. The latter is the action the two
  conclusions below carry as a `letI`, and it is named so that a consumer of those conclusions
  need not write the restriction of scalars out again.
* `AlgebraicGeometry.globalSectionsLinearEquivOfIso` is the `R`-linear equivalence on global
  sections induced by an isomorphism of modules.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_along_fibre` is Tag 05L0,
  from Tag 05KY and Tag 057B.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType`
  is Tag 05L1, the same conclusion for `f` merely of finite type, with the two
  finite-presentation clauses dropped, from Tag 05KZ and Tag 057B by the same argument.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sheaf_along_fibre` and
  `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sheaf_along_fibre_of_finiteType`
  restate those two conclusions with the freeness clause read as an isomorphism between the
  pushforward of `g^*F` to `Spec 𝒪_{S', s'}` and a free module on that affine scheme. In that
  form no restriction of scalars occurs, so the statements need no `letI`.
* `AlgebraicGeometry.globalSectionsModuleOfSpecBase_eq_pushforwardModule` and
  `AlgebraicGeometry.free_globalSections_iff_free_pushforward_globalSections` are what make that
  restatement possible: the restriction of scalars of the two conclusions *is* the action which
  the pushforward to `Spec 𝒪_{S', s'}`, being a module on an affine scheme, carries by instance.

## Implementation notes

The base of the new diagram is the spectrum of the stalk at the distinguished point of the
elementary étale neighbourhood, as in Tag 05KY, and the `𝒪_{S', s'}`-action on global sections is
restriction of scalars along the structure morphism composed with the canonical identification of
the ring with the global sections of its spectrum — that is,
`AlgebraicGeometry.globalSectionsModuleOfSpecBase`. The equality `X_s = g((X')_{s'})` is an
equality of subsets of `X`.

A morphism `V ⟶ U` of étale neighbourhoods of `s` induces `𝒪_{U, u} ⟶ 𝒪_{V, v}` on stalks and
hence `Spec 𝒪_{V, v} ⟶ Spec 𝒪_{U, u}` over `S`, which is how the charts are transported to the
dominating neighbourhood; the induced map carries closed point to closed point because the stalk
map is local.

Finite presentation of the pulled-back module on the coproduct is not available by Zariski
locality at the source, so it is obtained by descent along the fpqc cover given by the coproduct
inclusions, which are flat open immersions.

## References

* [Stacks Project, Tag 05L0](https://stacks.math.columbia.edu/tag/05L0)
* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
* [Stacks Project, Tag 05KY](https://stacks.math.columbia.edu/tag/05KY)
* [Stacks Project, Tag 05KZ](https://stacks.math.columbia.edu/tag/05KZ)
* [Stacks Project, Tag 057B](https://stacks.math.columbia.edu/tag/057B)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ElementaryEtaleFlatness
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The module of global sections over an affine base -/

/-- For a morphism `b : Z ⟶ Spec R` of schemes, the ring map `R ⟶ Γ(Z, ⊤)` it induces on global
sections: the canonical identification of `R` with the global sections of `Spec R`, followed by
`b` on global sections. -/
def specBaseScalars {R : CommRingCat.{u}} {Z : Scheme.{u}} (b : Z ⟶ Spec R) : R ⟶ Γ(Z, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ b.appTop

/-- The `R`-module structure on the global sections of a module `M` on a scheme `Z` over
`Spec R`: restriction of scalars along `AlgebraicGeometry.specBaseScalars`.

This is the action the conclusions of Tag 05L0 and Tag 05L1 below speak about. It cannot be an
instance, since it depends on the morphism `b`, which is why those conclusions carry it as a
`letI`; this definition is what that `letI` abbreviates, so a consumer need not spell the
restriction of scalars out again to use them. -/
@[instance_reducible, ega "I 2.2.5"]
def globalSectionsModuleOfSpecBase {R : CommRingCat.{u}} {Z : Scheme.{u}} (b : Z ⟶ Spec R)
    (M : Z.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom _ (specBaseScalars b).hom

/-- The action of `AlgebraicGeometry.globalSectionsModuleOfSpecBase` is the action of the image
of the scalar under `AlgebraicGeometry.specBaseScalars`. -/
theorem globalSectionsModuleOfSpecBase_smul {R : CommRingCat.{u}} {Z : Scheme.{u}}
    (b : Z ⟶ Spec R) (M : Z.Modules) (r : R) (x : Γ(M, ⊤)) :
    letI := globalSectionsModuleOfSpecBase b M
    r • x = (specBaseScalars b).hom r • x :=
  rfl

/-- **The restriction of scalars is the canonical action on the sections of the pushforward.**
The global sections of `M` over `Z` and of its pushforward along `b : Z ⟶ Spec R` are the same
group, and the `R`-action of `AlgebraicGeometry.globalSectionsModuleOfSpecBase` is the action
that the pushforward, being a module on `Spec R`, carries by instance. -/
theorem globalSectionsModuleOfSpecBase_eq_pushforwardModule {R : CommRingCat.{u}}
    {Z : Scheme.{u}} (b : Z ⟶ Spec R) (M : Z.Modules) :
    globalSectionsModuleOfSpecBase b M =
      inferInstanceAs (Module R Γ((Scheme.Modules.pushforward b).obj M, ⊤)) :=
  rfl

/-- Freeness of the global sections of the pushforward along `b : Z ⟶ Spec R`, for the action
`Spec R` supplies, is freeness of the global sections of `M` for the restriction of scalars of
`AlgebraicGeometry.globalSectionsModuleOfSpecBase`. This is the shape in which the freeness
clause of Tag 05L0 and Tag 05L1 is usable: the left-hand side needs no `letI`. -/
theorem free_globalSections_iff_free_pushforward_globalSections {R : CommRingCat.{u}}
    {Z : Scheme.{u}} (b : Z ⟶ Spec R) (M : Z.Modules) :
    Module.Free R Γ((Scheme.Modules.pushforward b).obj M, ⊤) ↔
      letI := globalSectionsModuleOfSpecBase b M
      Module.Free R Γ(M, ⊤) :=
  Iff.rfl

/-- **An isomorphism of modules is `R`-linear on global sections**, for the restriction of
scalars along a morphism `b : Z ⟶ Spec R`. -/
def globalSectionsLinearEquivOfIso {R : CommRingCat.{u}} {Z : Scheme.{u}} (b : Z ⟶ Spec R)
    {M N : Z.Modules} (e : M ≅ N) :
    letI := globalSectionsModuleOfSpecBase b M
    letI := globalSectionsModuleOfSpecBase b N
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) := by
  letI : Module R Γ(M, ⊤) := globalSectionsModuleOfSpecBase b M
  letI : Module R Γ(N, ⊤) := globalSectionsModuleOfSpecBase b N
  exact
    { Equiv.ofBijective (fun x => (e.hom.app ⊤) x)
        (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)) with
      map_add' := fun x y => map_add (e.hom.app ⊤).hom x y
      map_smul' := fun a x => Scheme.Modules.Hom.app_smul e.hom ((specBaseScalars b).hom a) x }

/-! ### Freeness of sections under affine base change -/

/-- A quasi-coherent module on an affine scheme with free global sections is a free module. -/
private lemma free_sheaf_of_free_sections (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Module.Free R Γ(M, ⊤)] :
    ∃ I : Type u, Nonempty (M ≅ SheafOfModules.free I) := by
  let I := Module.Free.ChooseBasisIndex R Γ(M, ⊤)
  let e : ModuleCat.of R Γ(M, ⊤) ≅ ModuleCat.of R (I →₀ R) :=
    (Module.Free.chooseBasis R Γ(M, ⊤)).repr.toModuleIso
  let eM : M ≅ SheafOfModules.free I :=
    (asIso M.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e ≪≫ tildeFinsupp I
  exact ⟨I, ⟨eM⟩⟩

/-- The pullback of a free module along a morphism of affine schemes is free on the same basis. -/
private def pullback_free_sheaf (R S : CommRingCat.{u}) (φ : R ⟶ S) (I : Type u) :
    (Scheme.Modules.pullback (Spec.map φ)).obj
        (SheafOfModules.free I : (Spec R).Modules) ≅
      (SheafOfModules.free I : (Spec S).Modules) := by
  letI : (TopologicalSpace.Opens.map (Spec.map φ).base).Final :=
    CategoryTheory.final_of_representablyFlat _
  letI : (SheafOfModules.pushforward (Spec.map φ).toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).isRightAdjoint
  exact SheafOfModules.pullbackObjFreeIso (Spec.map φ).toRingCatSheafHom I

/-- The global sections of a free module on an affine scheme are a free module. -/
private lemma free_sections_of_free_sheaf (R : CommRingCat.{u}) (I : Type u) :
    letI : Module R Γ((SheafOfModules.free I : (Spec R).Modules), ⊤) :=
      inferInstanceAs <| Module R
        ((modulesSpecToSheaf.obj (SheafOfModules.free I : (Spec R).Modules)).obj.obj (.op ⊤))
    Module.Free R Γ((SheafOfModules.free I : (Spec R).Modules), ⊤) := by
  let : Module R Γ((SheafOfModules.free I : (Spec R).Modules), ⊤) :=
    inferInstanceAs <| Module R
      ((modulesSpecToSheaf.obj (SheafOfModules.free I : (Spec R).Modules)).obj.obj (.op ⊤))
  let e := (tilde.isoTop (ModuleCat.of R (I →₀ R))).trans
    ((moduleSpecΓFunctor (R := R)).mapIso (tildeFinsupp I))
  exact Module.Free.of_equiv e.toLinearEquiv

/-- **Freeness of sections survives affine base change.** If the direct image of a quasi-coherent
module along an affine morphism `q : Y ⟶ Spec R` has free global sections, then so does the direct
image of its pullback along the base change of `q` by `Spec S ⟶ Spec R`. -/
private lemma free_after_affine_base_change (R S : CommRingCat.{u})
    (φ : R ⟶ S) {Y : Scheme.{u}} [IsAffine Y]
    (q : Y ⟶ Spec R) (N : Y.Modules) [N.IsQuasicoherent]
    [Module.Free R Γ((Scheme.Modules.pushforward q).obj N, ⊤)] :
    Module.Free S Γ((Scheme.Modules.pushforward (pullback.snd q (Spec.map φ))).obj
      ((Scheme.Modules.pullback (pullback.fst q (Spec.map φ))).obj N), ⊤) := by
  let : IsAffineHom q := inferInstance
  let e := affinePushforwardBaseChangeIso (IsPullback.of_hasPullback q (Spec.map φ)) N
  obtain ⟨I, ⟨eFree⟩⟩ := free_sheaf_of_free_sections R
    ((Scheme.Modules.pushforward q).obj N)
  let e' : (Scheme.Modules.pushforward (pullback.snd q (Spec.map φ))).obj
      ((Scheme.Modules.pullback (pullback.fst q (Spec.map φ))).obj N) ≅
      (SheafOfModules.free I : (Spec S).Modules) :=
    e.symm ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso eFree ≪≫
      pullback_free_sheaf R S φ I
  let : Module S Γ((SheafOfModules.free I : (Spec S).Modules), ⊤) :=
    inferInstanceAs <| Module S
      ((modulesSpecToSheaf.obj (SheafOfModules.free I : (Spec S).Modules)).obj.obj (.op ⊤))
  let : Module.Free S Γ((SheafOfModules.free I : (Spec S).Modules), ⊤) :=
    free_sections_of_free_sheaf S I
  have : Module.Free S (moduleSpecΓFunctor.obj
      (SheafOfModules.free I : (Spec S).Modules)) := by
    change Module.Free S Γ((SheafOfModules.free I : (Spec S).Modules), ⊤)
    infer_instance
  exact Module.Free.of_equiv ((moduleSpecΓFunctor (R := S)).mapIso e').symm.toLinearEquiv

/-- **Freeness of sections transports along an isomorphism of modules**, for the scalar action
restricted from a ring to the global sections of a scheme over its spectrum. -/
private alias free_sections_of_module_iso := free_globalSections_of_moduleIso

/-- **Freeness of the sections of a pullback to an affine base change.** If the pullback of `F` to
an affine scheme `Y` over `Spec R` has free sections over `R`, then its further pullback to the
base change of `Y` along `Spec S ⟶ Spec R` has free sections over `S`. -/
private lemma free_sections_pullback_base_change (R S : CommRingCat.{u}) (φ : R ⟶ S)
    {X Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ Spec R) (g₀ : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] (g : pullback q (Spec.map φ) ⟶ X)
    (hg : pullback.fst q (Spec.map φ) ≫ g₀ = g)
    (hfree :
      letI : Module R Γ((Scheme.Modules.pullback g₀).obj F, ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
      Module.Free R Γ((Scheme.Modules.pullback g₀).obj F, ⊤)) :
    letI : Module S Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso S).inv ≫ (pullback.snd q (Spec.map φ)).appTop).hom
    Module.Free S Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  subst hg
  have : ((Scheme.Modules.pullback g₀).obj F).IsQuasicoherent := pullback_isQuasicoherent' g₀ F
  have : Module.Free R Γ((Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback g₀).obj F), ⊤) := hfree
  exact free_sections_of_module_iso S _ _ _
    ((Scheme.Modules.pullbackComp (pullback.fst q (Spec.map φ)) g₀).app F)
    (free_after_affine_base_change R S φ q ((Scheme.Modules.pullback g₀).obj F))

/-! ### Charts at the points of the fibre -/

/-- Open neighbourhoods chosen at every point of a quasi-compact fibre admit a finite
subcover. -/
private lemma finite_fiber_chart_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] (s : S) {ι : Type*} (W : ι → Set (f.fiber s))
    (hopen : ∀ i, IsOpen (W i)) (hcover : ∀ x, ∃ i, x ∈ W i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, x ∈ W i := by
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set (f.fiber s))).elim_finite_subcover
    W hopen fun x _ => Set.mem_iUnion.mpr (hcover x)
  refine ⟨t, fun x => ?_⟩
  obtain ⟨i, hi, hWi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨i, hi, hWi⟩

/-- **Tag 05KY in chart form.** At a point of the fibre `X_s` there are an elementary étale
neighbourhood `(S', s')` of `(S, s)` and an affine scheme `Y` étale over
`X ×_S Spec 𝒪_{S', s'}` whose chart hits the point over the closed point, is of finite
presentation over `𝒪_{S', s'}`, and carries free sections of the pullback of `F`. -/
private lemma local_chart_at_fiber_point {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (x : f.fiber s)
    (hflat : ∀ y : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (Y : Scheme.{u}) (y : Y)
      (p : Y ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase))
      (_ : Etale p) (_ : IsAffine Y)
      (_ : (p ≫ pullback.fst f
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y = f.fiberι s x)
      (_ : (p ≫ pullback.snd f
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y =
          IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (_ : FinitePresentation (p ≫ pullback.snd f
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)))
      (_ : ((Scheme.Modules.pullback
        (p ≫ pullback.fst f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback
            (p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫
            (p ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback
          (p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F, ⊤) := by
  have hs : f (f.fiberι s x) = s := (f.range_fiberι s).subset (Set.mem_range_self x)
  have h := exists_etale_neighborhood_with_free_globalSections_of_isFiniteType
    f F (f.fiberι s x) (hflat x)
  rw [hs] at h
  rcases h with ⟨U, hU, Y, y, g, q, hyx, hyq, hcomm, het, hres, hAff, hqfp, hFfp, hfree⟩
  let p := pullback.lift g q hcomm
  have hpFst : p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) = g :=
    pullback.lift_fst _ _ _
  have hpSnd : p ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) = q :=
    pullback.lift_snd _ _ _
  refine ⟨U, hU, Y, y, p, by simpa only [p] using het, hAff, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hpFst]
  · rwa [hpSnd]
  · rwa [hpSnd]
  · rwa [hpFst]
  · rw [hpFst, hpSnd]
    exact hfree

/-- **Tag 057B in the form used here.** Finitely many elementary étale neighbourhoods of a point
are dominated by a single elementary étale neighbourhood, the category of those being
cofiltered. -/
private lemma finite_common_elementary_neighborhood {S : Scheme.{u}} (s : S)
    {ι : Type*} (t : Finset ι) (U : ι → EtaleNeighborhood S s)
    (hU : ∀ i, (U i).IsElementary) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧ ∀ i ∈ t, Nonempty (V ⟶ U i) := by
  classical
  let W : ι → ElementaryEtaleNeighborhood S s := fun i => ⟨U i, hU i⟩
  let : IsCofiltered (ElementaryEtaleNeighborhood S s) :=
    isCofiltered_of_isFiltered_op _
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (t.image W)
  exact ⟨V.obj, V.property, fun i hi => ⟨(hV (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).some.hom⟩⟩

/-! ### Transporting a chart to a dominating neighbourhood -/

/-- The map on stalks at the distinguished points induced by a morphism of étale neighbourhoods
of a point. -/
private def neighborhoodStalkMap {S : Scheme.{u}} {s : S}
    {V U : EtaleNeighborhood S s} (h : V ⟶ U) :
    U.scheme.presheaf.stalk U.point ⟶ V.scheme.presheaf.stalk V.point :=
  (U.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom ≫ h.hom.stalkMap V.point

/-- The spectrum of the induced stalk map commutes with the canonical morphisms from the spectra
of the stalks. -/
private lemma neighborhoodStalkMap_fromSpecStalk {S : Scheme.{u}} {s : S}
    {V U : EtaleNeighborhood S s} (h : V ⟶ U) :
    Spec.map (neighborhoodStalkMap h) ≫ U.scheme.fromSpecStalk U.point =
      V.scheme.fromSpecStalk V.point ≫ h.hom := by
  rw [neighborhoodStalkMap, Spec.map_comp, Category.assoc,
    show Spec.map (U.scheme.presheaf.stalkCongr (.of_eq h.map_point.symm)).hom ≫
        U.scheme.fromSpecStalk U.point = U.scheme.fromSpecStalk (h.hom V.point) from
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq h.map_point.symm).ge,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The spectrum of the induced stalk map is a morphism over the base. -/
private lemma neighborhoodStalkMap_over_base {S : Scheme.{u}} {s : S}
    {V U : EtaleNeighborhood S s} (h : V ⟶ U) :
    Spec.map (neighborhoodStalkMap h) ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase =
      V.scheme.fromSpecStalk V.point ≫ V.toBase := by
  rw [← Category.assoc, neighborhoodStalkMap_fromSpecStalk, Category.assoc, h.over]

/-- The spectrum of the induced stalk map sends closed point to closed point. -/
private lemma neighborhoodStalkMap_closedPoint {S : Scheme.{u}} {s : S}
    {V U : EtaleNeighborhood S s} (h : V ⟶ U) :
    Spec.map (neighborhoodStalkMap h)
        (IsLocalRing.closedPoint (V.scheme.presheaf.stalk V.point)) =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) := by
  have : IsLocalHom (neighborhoodStalkMap h).hom := by
    unfold neighborhoodStalkMap
    infer_instance
  exact Spec_closedPoint

/-- The closed point of the spectrum of the stalk of an étale neighbourhood lies over the point
of which it is a neighbourhood. -/
private lemma neighborhood_closedPoint_over_base {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) :
    (U.scheme.fromSpecStalk U.point ≫ U.toBase)
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) = s :=
  (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg U.toBase (Scheme.fromSpecStalk_closedPoint (X := U.scheme)
      (x := U.point))).trans U.map_point)

/-- The structure morphism of `Spec 𝒪_{S', s'}` over `S` is an isomorphism on the residue field at
the closed point when `(S', s')` is an elementary étale neighbourhood. -/
theorem neighborhood_base_residueFieldMap_isIso {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) [U.IsElementary] :
    IsIso ((U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap
      (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) := by
  have hU : IsIso (U.toBase.residueFieldMap U.point) := by
    have h : IsIso U.residueFieldMap := inferInstance
    unfold EtaleNeighborhood.residueFieldMap at h
    exact IsIso.of_isIso_comp_left (S.residueFieldCongr U.map_point).inv
      (U.toBase.residueFieldMap U.point)
  have hbase : IsIso (U.toBase.residueFieldMap
      (U.scheme.fromSpecStalk U.point
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)))) := by
    have he : U.scheme.fromSpecStalk U.point
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) = U.point :=
      Scheme.fromSpecStalk_closedPoint
    exact cast (congrArg (fun z => IsIso (U.toBase.residueFieldMap z)) he).symm hU
  have hc := Scheme.residueFieldMap_comp (U.scheme.fromSpecStalk U.point) U.toBase
    (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
  rw [hc]
  exact IsIso.comp_isIso' hbase
    (AlgebraicGeometry.ElementaryEtaleFlatness.fromSpecStalk_residueFieldMap_closedPoint_isIso
      U.scheme U.point)

/-! ### The fibre of a base change over a point -/

/-- The morphism of fibres induced by a chart over the base change. -/
private def chartFiberMap {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (p : Y ⟶ pullback f a) (t : T) :
    (p ≫ pullback.snd f a).fiber t ⟶ (pullback.snd f a).fiber t :=
  pullback.map _ _ _ _ p (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The map of base changes along `r` induced by an étale chart `p` is étale. -/
private lemma etale_pullback_map_chart {X S T T' Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (r : T' ⟶ T) (p : Y ⟶ pullback f a) (q : Y ⟶ T)
    (hq : p ≫ pullback.snd f a = q) [Etale p] :
    Etale (pullback.map q r (pullback.snd f a) r p (𝟙 _) (𝟙 _) (by simp [hq]) (by simp)) := by
  apply MorphismProperty.pullbackMap (P := @Etale)
  · exact ‹Etale p›
  · infer_instance
  · simp [hq]
  · simp

/-- The morphism of fibres induced by an étale chart is étale. -/
private lemma chartFiberMap_etale {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (p : Y ⟶ pullback f a) (t : T)
    [Etale p] : Etale (chartFiberMap f a p t) :=
  etale_pullback_map_chart f a _ p _ rfl

/-- The morphism of fibres induced by a chart is compatible with the inclusions of the fibres. -/
private lemma chartFiberMap_fiberι {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (p : Y ⟶ pullback f a) (t : T) :
    chartFiberMap f a p t ≫ (pullback.snd f a).fiberι t =
      (p ≫ pullback.snd f a).fiberι t ≫ p := by
  simp only [chartFiberMap, pullback.map, Category.comp_id, Scheme.Hom.fiberι]
  exact pullback.lift_fst _ _ _

/-- The image in the fibre of the original morphism of the fibre of an étale chart is open. -/
private lemma isOpen_range_chartFiberMap {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (p : Y ⟶ pullback f a) (t : T)
    [Etale p] [IsIso (a.residueFieldMap t)] :
    IsOpen (Set.range (chartFiberMap f a p t ≫ baseChangeFiberMap f a t)) := by
  have : Etale (chartFiberMap f a p t) := chartFiberMap_etale f a p t
  have : IsIso (baseChangeFiberMap f a t) := isIso_baseChangeFiberMap f a t
  have : Etale (baseChangeFiberMap f a t) := inferInstance
  have : Etale (chartFiberMap f a p t ≫ baseChangeFiberMap f a t) := inferInstance
  exact (chartFiberMap f a p t ≫ baseChangeFiberMap f a t).isOpenMap.isOpen_range

/-- The set of points of the fibre `X_{a t}` hit by an étale chart over `t` is open. -/
private lemma isOpen_chart_closedFiber_image {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (p : Y ⟶ pullback f a) (t : T)
    [Etale p] [IsIso (a.residueFieldMap t)] :
    IsOpen {x : f.fiber (a t) |
      ∃ y : Y, (p ≫ pullback.snd f a) y = t ∧
        (p ≫ pullback.fst f a) y = f.fiberι (a t) x} := by
  let q : Y ⟶ T := p ≫ pullback.snd f a
  let g : Y ⟶ X := p ≫ pullback.fst f a
  let m : q.fiber t ⟶ f.fiber (a t) :=
    chartFiberMap f a p t ≫ baseChangeFiberMap f a t
  have hm : m ≫ f.fiberι (a t) = q.fiberι t ≫ g := by
    dsimp [m, q, g]
    rw [Category.assoc, baseChangeFiberMap_comp_fiberι, ← Category.assoc,
      chartFiberMap_fiberι, Category.assoc]
  have hW : {x : f.fiber (a t) | ∃ y : Y, q y = t ∧ g y = f.fiberι (a t) x} =
      Set.range m := by
    ext x
    constructor
    · rintro ⟨y, hy, hgy⟩
      let z : q.fiber t := (q.fiberHomeo t).symm ⟨y, hy⟩
      refine ⟨z, ?_⟩
      apply (f.fiberι (a t)).isEmbedding.injective
      have hz : q.fiberι t z = y := q.fiberι_fiberHomeo_symm t ⟨y, hy⟩
      have he := congrArg (fun k : q.fiber t ⟶ X => k z) hm
      simpa only [Scheme.Hom.comp_apply, hz, hgy] using he
    · rintro ⟨z, rfl⟩
      refine ⟨q.fiberι t z, ?_, ?_⟩
      · have h := congrArg (fun k : q.fiber t ⟶ T => k z) (q.fiber_fac t)
        simpa [Scheme.Hom.comp_apply] using h
      · have h := congrArg (fun k : q.fiber t ⟶ X => k z) hm
        simpa [Scheme.Hom.comp_apply] using h.symm
  rw [hW]
  exact isOpen_range_chartFiberMap f a p t

/-- The set of points of `X_s` hit by an étale chart over the closed point of
`Spec 𝒪_{S', s'}` is open, for `(S', s')` an elementary étale neighbourhood of `(S, s)`. -/
private lemma isOpen_local_chart_fiber_image {X S Y : Scheme.{u}}
    (f : X ⟶ S) (s : S) (U : EtaleNeighborhood S s) [U.IsElementary]
    (p : Y ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) [Etale p] :
    IsOpen {x : f.fiber s |
      ∃ y : Y, (p ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y =
          IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) ∧
        (p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y =
          f.fiberι s x} := by
  let a := U.scheme.fromSpecStalk U.point ≫ U.toBase
  let t := IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)
  have : IsIso (a.residueFieldMap t) := neighborhood_base_residueFieldMap_isIso U
  have h := isOpen_chart_closedFiber_image f a p t
  have hat : a t = s := neighborhood_closedPoint_over_base U
  rwa [hat] at h

/-- The image of the fibre over a point of the base lies in the fibre over its image. -/
private lemma image_closed_fiber_subset {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (g : Y ⟶ X) (p : Y ⟶ T)
    (hcomm : g ≫ f = p ≫ b) (t : T) :
    g '' (p ⁻¹' {t}) ⊆ f ⁻¹' {b t} := by
  rintro x ⟨y, hy, rfl⟩
  change f (g y) = b t
  have h := congrArg (fun (k : Y ⟶ S) => k y) hcomm
  change p y = t at hy
  simpa only [Scheme.Hom.comp_apply, hy] using h

/-- The base change of a chart over the base change of its base. -/
private def baseChangeChartMap {X S T T' Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (r : T' ⟶ T) (p : Y ⟶ pullback f a) :
    pullback (p ≫ pullback.snd f a) r ⟶ pullback f (r ≫ a) :=
  pullback.lift
    (pullback.fst (p ≫ pullback.snd f a) r ≫ p ≫ pullback.fst f a)
    (pullback.snd (p ≫ pullback.snd f a) r)
    (by
      calc
        (pullback.fst (p ≫ pullback.snd f a) r ≫ p ≫ pullback.fst f a) ≫ f =
            pullback.fst (p ≫ pullback.snd f a) r ≫ p ≫ pullback.snd f a ≫ a := by
              simp only [Category.assoc, pullback.condition]
        _ = pullback.snd (p ≫ pullback.snd f a) r ≫ (r ≫ a) := by
              have hc : pullback.fst (p ≫ pullback.snd f a) r ≫
                  (p ≫ pullback.snd f a) =
                  pullback.snd (p ≫ pullback.snd f a) r ≫ r := pullback.condition
              simpa only [Category.assoc] using congrArg (fun k => k ≫ a) hc)

/-- The base change of an étale chart is étale. -/
private lemma baseChangeChartMap_etale {X S T T' Y : Scheme.{u}}
    (f : X ⟶ S) (a : T ⟶ S) (r : T' ⟶ T) (p : Y ⟶ pullback f a) [Etale p] :
    Etale (baseChangeChartMap f a r p) := by
  let q : Y ⟶ T := p ≫ pullback.snd f a
  let b : pullback q r ⟶ pullback (pullback.snd f a) r :=
    pullback.map q r (pullback.snd f a) r p (𝟙 _) (𝟙 _) (by simp [q]) (by simp)
  have hb : Etale b := etale_pullback_map_chart f a r p q rfl
  have he : baseChangeChartMap f a r p = b ≫ (pullbackLeftPullbackSndIso f a r).hom := by
    apply pullback.hom_ext
    · simp [baseChangeChartMap, b, pullback.map, q, Category.assoc]
    · simp [baseChangeChartMap, b, pullback.map, q, Category.assoc]
  rw [he]
  exact MorphismProperty.comp_mem @Etale _ _ hb inferInstance

/-! ### Properties of a finite coproduct of charts -/

/-- A morphism out of a coproduct is étale when each of its components is. -/
private lemma etale_sigma_desc {ι : Type u} (X : Scheme.{u})
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i)] : Etale (Sigma.desc f) := by
  let : HasRingHomProperty @Etale RingHom.Etale := inferInstance
  let : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)

/-- A morphism out of a coproduct is locally of finite presentation when each of its components
is. -/
private lemma locallyOfFinitePresentation_sigma_desc {ι : Type u} {X : Scheme.{u}}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFinitePresentation (f i)] :
    LocallyOfFinitePresentation (Sigma.desc f) := by
  let : HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation :=
    inferInstance
  let : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
    (fun _ => inferInstance)

/-- A morphism from an affine coproduct of charts to an affine base is of finite presentation as
soon as it is locally of finite presentation. -/
private lemma finitePresentation_sigma_desc {ι : Type u} {T : Scheme.{u}} [IsAffine T]
    (Z : ι → Scheme.{u}) [∀ i, IsAffine (Z i)] [Finite ι] (qChart : ∀ i, Z i ⟶ T)
    (hq : ∀ i, LocallyOfFinitePresentation (qChart i)) :
    FinitePresentation (Sigma.desc qChart) := by
  have : IsAffine (∐ Z) := inferInstance
  have (i : ι) : LocallyOfFinitePresentation (qChart i) := hq i
  have hlfp : LocallyOfFinitePresentation (Sigma.desc qChart) :=
    locallyOfFinitePresentation_sigma_desc qChart
  let : IsAffineHom (Sigma.desc qChart) := inferInstance
  exact FinitePresentation.mk hlfp inferInstance inferInstance

/-- The componentwise restriction map on global sections of a pullback is additive. -/
private lemma componentSectionMap_add {ι : Type u} (Y : ι → Scheme.{u})
    {X : Scheme.{u}} (g₀ : ∀ i, Y i ⟶ X) (F : X.Modules) (i : ι)
    (x y : Γ((Scheme.Modules.pullback (Sigma.desc g₀)).obj F, ⊤)) :
    let M := (Scheme.Modules.pullback (Sigma.desc g₀)).obj F
    let q (z : Γ(M, ⊤)) :=
      (componentSectionIso Y g₀ F i).hom
        (M.presheaf.map (homOfLE (le_top : Sigma.ι Y i ''ᵁ ⊤ ≤ ⊤)).op z)
    q (x + y) = q x + q y := by
  simp [map_add]

/-- A module which is linearly isomorphic to a finite product of free modules is free. -/
private lemma free_of_component_bijection {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (P : ι → Type u) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, Module.Free R (P i)] {M : Type u} [AddCommGroup M] [Module R M]
    (q : M → (∀ i, P i)) (hq : Function.Bijective q)
    (hadd : ∀ x y, q (x + y) = q x + q y)
    (hsmul : ∀ (r : R) (x : M), q (r • x) = r • q x) : Module.Free R M := by
  let e : M ≃ₗ[R] (∀ i, P i) :=
    { Equiv.ofBijective q hq with
      map_add' := hadd
      map_smul' := hsmul }
  let : Module.Free R (∀ i, P i) := Module.Free.pi R P
  exact Module.Free.of_equiv e.symm

/-- **Global sections of the pullback to a finite coproduct are free over an external base** when
the sections on each component are, the morphism to the base restricting on each component to the
given one. -/
private lemma free_globalSections_sigma {ι : Type u} [Finite ι] {X : Scheme.{u}}
    (R : CommRingCat.{u}) (Z : ι → Scheme.{u}) (gChart : ∀ i, Z i ⟶ X) (F : X.Modules)
    (c : (∐ Z) ⟶ Spec R) (b : ∀ i, Z i ⟶ Spec R)
    (hbc : ∀ i, Sigma.ι Z i ≫ c = b i)
    (hfree : ∀ i,
      letI : Module R Γ((Scheme.Modules.pullback (gChart i)).obj F, ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (b i).appTop).hom
      Module.Free R Γ((Scheme.Modules.pullback (gChart i)).obj F, ⊤)) :
    letI : Module R Γ((Scheme.Modules.pullback (Sigma.desc gChart)).obj F, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ c.appTop).hom
    Module.Free R Γ((Scheme.Modules.pullback (Sigma.desc gChart)).obj F, ⊤) := by
  let B (i : ι) := Γ((Scheme.Modules.pullback (gChart i)).obj F, ⊤)
  let (i : ι) : Module R (B i) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ (b i).appTop).hom
  have (i : ι) : Module.Free R (B i) := hfree i
  let M := (Scheme.Modules.pullback (Sigma.desc gChart)).obj F
  let : Module R Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ c.appTop).hom
  let qSection : Γ(M, ⊤) → (∀ i, B i) := fun x i =>
    (componentSectionIso Z gChart F i).hom
      (M.presheaf.map (homOfLE (le_top : Sigma.ι Z i ''ᵁ ⊤ ≤ ⊤)).op x)
  have hbij : Function.Bijective qSection := componentSectionMap_bijective Z gChart F
  have hadd : ∀ x y, qSection (x + y) = qSection x + qSection y := fun x y =>
    funext fun i => componentSectionMap_add Z gChart F i x y
  have hsmul : ∀ (a : R) (x : Γ(M, ⊤)), qSection (a • x) = a • qSection x := by
    intro a x
    funext i
    have hc : Sigma.ι Z i ≫ c = b i ≫ 𝟙 (Spec R) := (hbc i).trans (Category.comp_id _).symm
    have hh := componentSectionMap_smul Z gChart F c (b i) (𝟙 (Spec R)) hc
      ((Scheme.ΓSpecIso R).inv.hom a) x
    change qSection (((Scheme.ΓSpecIso R).inv ≫ c.appTop).hom a • x) i =
      (((Scheme.ΓSpecIso R).inv ≫ (b i).appTop).hom a) • qSection x i
    simpa [qSection, Scheme.Hom.id_appTop, Scheme.Hom.comp_appTop] using hh
  exact free_of_component_bijection (R := R) (M := Γ(M, ⊤))
    (fun i => (B i : Type u)) qSection hbij hadd hsmul

/-- **Finite presentation of the pullback to a coproduct.** Finite presentation is not local at
the source for modules, so it is descended along the fpqc cover given by the coproduct
inclusions, which are flat open immersions. -/
private lemma isFinitePresentation_sigma {ι : Type u} {X : Scheme.{u}}
    (Z : ι → Scheme.{u}) (gChart : ∀ i, Z i ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
    (hcomp : ∀ i, ((Scheme.Modules.pullback (gChart i)).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback (Sigma.desc gChart)).obj F).IsFinitePresentation := by
  classical
  let M := (Scheme.Modules.pullback (Sigma.desc gChart)).obj F
  have : M.IsQuasicoherent := pullback_isQuasicoherent' (Sigma.desc gChart) F
  let O : ι → (∐ Z).Opens := fun i => Sigma.ι Z i ''ᵁ ⊤
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover (g := Z)).iSup_opensRange
  have hmemrange (x : ↑(∐ Z : Scheme.{u})) : ∃ i, ∃ z : Z i, Sigma.ι Z i z = x := by
    have hx : x ∈ (⊤ : (∐ Z).Opens) := by simp
    rw [← hO] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hi' : x ∈ (Sigma.ι Z i).opensRange := by
      simpa [O, Scheme.Hom.image_top_eq_opensRange] using hi
    obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hi'
    exact ⟨i, z, hz⟩
  have hcomponentFP (i : ι) :
      ((Scheme.Modules.pullback (Sigma.ι Z i)).obj M).IsFinitePresentation := by
    let he : ((Scheme.Modules.pullback (Sigma.ι Z i)).obj M) ≅
        (Scheme.Modules.pullback (gChart i)).obj F :=
      ((Scheme.Modules.restrictFunctorIsoPullback (Sigma.ι Z i)).app M).symm ≪≫
        componentModuleIso Z gChart F i
    exact (SheafOfModules.isFinitePresentation (Z i).ringCatSheaf).prop_of_iso
      he.symm (hcomp i)
  let E : PreZeroHypercover (∐ Z) := ⟨ι, Z, Sigma.ι Z⟩
  let 𝒰 : (∐ Z).Cover Scheme.fpqcPrecoverage := by
    refine ⟨E, ?_⟩
    change E.presieve₀ ∈
      (Scheme.qcPrecoverage ⊓ Scheme.precoverage (@Flat : MorphismProperty Scheme)) _
    constructor
    · apply Scheme.precoverage_le_qcPrecoverage_of_isOpenMap
        (P := @IsOpenImmersion) (fun _ _ f _ => f.isOpenMap) (∐ Z)
      apply (Scheme.presieve₀_mem_precoverage_iff (P := @IsOpenImmersion) E).2
      refine ⟨fun x => ?_, fun i => inferInstance⟩
      obtain ⟨i, z, hz⟩ := hmemrange x
      exact ⟨i, ⟨z, hz⟩⟩
    · apply (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) E).2
      refine ⟨fun x => ?_, fun i => inferInstance⟩
      obtain ⟨i, z, hz⟩ := hmemrange x
      exact ⟨i, ⟨z, hz⟩⟩
  exact isFinitePresentation_of_pullback_fpqcCover M 𝒰 hcomponentFP

/-- **The shared construction of Tags 05L0 and 05L1.** Given, at every point of the fibre `X_s`, an
étale affine chart over `X ×_S Spec 𝒪_{S_x, s_x}` hitting that point over the closed point and with
free sections, there are an elementary étale neighbourhood `(S', s')` dominating them all and an
affine `X'` over `Spec 𝒪_{S', s'}` with the properties of Tag 05L1, the finite presentation clauses
of Tag 05L0 following from those of the charts. -/
private lemma exists_free_sections_of_charts {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] (s : S)
    (U : f.fiber s → EtaleNeighborhood S s) (hU : ∀ x, (U x).IsElementary)
    (Y : f.fiber s → Scheme.{u}) (y : ∀ x, Y x)
    (p : ∀ x, Y x ⟶ pullback f ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase))
    (hp : ∀ x, Etale (p x)) (hAff : ∀ x, IsAffine (Y x))
    (hx : ∀ x, (p x ≫ pullback.fst f
      ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase)) (y x) = f.fiberι s x)
    (hy : ∀ x, (p x ≫ pullback.snd f
      ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase)) (y x) =
        IsLocalRing.closedPoint ((U x).scheme.presheaf.stalk (U x).point))
    (hfree : ∀ x,
      letI : Module ((U x).scheme.presheaf.stalk (U x).point)
          Γ((Scheme.Modules.pullback (p x ≫ pullback.fst f
            ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase))).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of ((U x).scheme.presheaf.stalk (U x).point))).inv ≫
            (p x ≫ pullback.snd f
              ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase)).appTop).hom
      Module.Free ((U x).scheme.presheaf.stalk (U x).point)
        Γ((Scheme.Modules.pullback (p x ≫ pullback.fst f
          ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase))).obj F, ⊤)) :
    ∃ (V : EtaleNeighborhood S s) (_ : V.IsElementary)
      (X' : Scheme.{u})
      (q : X' ⟶ Spec (.of (V.scheme.presheaf.stalk V.point)))
      (g : X' ⟶ X)
      (hcomm : g ≫ f = q ≫ V.scheme.fromSpecStalk V.point ≫ V.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : f ⁻¹' {s} = g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X')
      (_ : (∀ x, FinitePresentation (p x ≫ pullback.snd f
        ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase))) → FinitePresentation q)
      (_ : (∀ x, ((Scheme.Modules.pullback (p x ≫ pullback.fst f
        ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase))).obj F).IsFinitePresentation) →
          ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (V.scheme.presheaf.stalk V.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (V.scheme.presheaf.stalk V.point))).inv ≫ q.appTop).hom
      Module.Free (V.scheme.presheaf.stalk V.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  classical
  let W : f.fiber s → Set (f.fiber s) := fun x =>
    {z | ∃ y' : Y x,
      (p x ≫ pullback.snd f ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase)) y' =
        IsLocalRing.closedPoint ((U x).scheme.presheaf.stalk (U x).point) ∧
      (p x ≫ pullback.fst f ((U x).scheme.fromSpecStalk (U x).point ≫ (U x).toBase)) y' =
        f.fiberι s z}
  have hopen (x : f.fiber s) : IsOpen (W x) := by
    let : (U x).IsElementary := hU x
    let : Etale (p x) := hp x
    exact isOpen_local_chart_fiber_image f s (U x) (p x)
  have hcover (z : f.fiber s) : ∃ x, z ∈ W x := ⟨z, y z, hy z, hx z⟩
  obtain ⟨t, ht⟩ := finite_fiber_chart_cover f s W hopen hcover
  obtain ⟨V, hV, hdom⟩ := finite_common_elementary_neighborhood s t U hU
  let ι := {x : f.fiber s // x ∈ t}
  let : Finite ι := inferInstance
  let h (i : ι) : V ⟶ U i.1 := (hdom i.1 i.2).some
  let aMap (i : ι) : Spec (.of ((U i.1).scheme.presheaf.stalk (U i.1).point)) ⟶ S :=
    (U i.1).scheme.fromSpecStalk (U i.1).point ≫ (U i.1).toBase
  let T : Scheme.{u} := Spec (.of (V.scheme.presheaf.stalk V.point))
  let aV : T ⟶ S := V.scheme.fromSpecStalk V.point ≫ V.toBase
  let r (i : ι) : T ⟶ Spec (.of ((U i.1).scheme.presheaf.stalk (U i.1).point)) :=
    Spec.map (neighborhoodStalkMap (h i))
  have hr (i : ι) : r i ≫ aMap i = aV := neighborhoodStalkMap_over_base (h i)
  let q (i : ι) : Y i.1 ⟶ Spec (.of ((U i.1).scheme.presheaf.stalk (U i.1).point)) :=
    p i.1 ≫ pullback.snd f (aMap i)
  let Z (i : ι) : Scheme.{u} := pullback (q i) (r i)
  have (i : ι) : IsAffine (Y i.1) := hAff i.1
  have (i : ι) : Etale (p i.1) := hp i.1
  have (i : ι) : IsAffine (Z i) := by
    dsimp [Z]
    infer_instance
  have : IsAffine (∐ Z) := inferInstance
  let pChart (i : ι) : Z i ⟶ pullback f aV :=
    baseChangeChartMap f (aMap i) (r i) (p i.1) ≫ (pullback.congrHom rfl (hr i)).hom
  have (i : ι) : Etale (pChart i) := by
    dsimp [pChart]
    exact MorphismProperty.comp_mem @Etale _ _
      (baseChangeChartMap_etale f (aMap i) (r i) (p i.1)) inferInstance
  let P : (∐ Z) ⟶ pullback f aV := Sigma.desc pChart
  have : Etale P := etale_sigma_desc _ Z pChart
  have hpChart_fst (i : ι) : pChart i ≫ pullback.fst f aV =
      pullback.fst (q i) (r i) ≫ p i.1 ≫ pullback.fst f (aMap i) := by
    simp [pChart, baseChangeChartMap, pullback.congrHom, Category.assoc]
    simp only [← Category.assoc]
    rfl
  have hpChart_snd (i : ι) : pChart i ≫ pullback.snd f aV =
      pullback.snd (q i) (r i) := by
    simp [pChart, baseChangeChartMap, pullback.congrHom, Category.assoc]
    rfl
  have hcomm : (P ≫ pullback.fst f aV) ≫ f = (P ≫ pullback.snd f aV) ≫ aV := by
    simp only [Category.assoc, pullback.condition]
  let gChart (i : ι) : Z i ⟶ X := pChart i ≫ pullback.fst f aV
  have hdescG : Sigma.desc gChart = P ≫ pullback.fst f aV := by
    apply Sigma.hom_ext
    intro i
    simp [gChart, P, ← Category.assoc]
  let qChart (i : ι) : Z i ⟶ T := pullback.snd (q i) (r i)
  have hdescQ : Sigma.desc qChart = P ≫ pullback.snd f aV := by
    apply Sigma.hom_ext
    intro i
    simp [qChart, P, ← Category.assoc, hpChart_snd]
  refine ⟨V, hV, ∐ Z, P ≫ pullback.snd f aV,
    P ≫ pullback.fst f aV, hcomm, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [show pullback.lift (P ≫ pullback.fst f aV) (P ≫ pullback.snd f aV) hcomm = P from
      pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)]
    infer_instance
  · let tV : T := IsLocalRing.closedPoint (V.scheme.presheaf.stalk V.point)
    apply Set.Subset.antisymm
    · intro z₀ hz₀
      let z : f.fiber s := (f.fiberHomeo s).symm ⟨z₀, hz₀⟩
      obtain ⟨i, hi, hzi⟩ := ht z
      let j : ι := ⟨i, hi⟩
      obtain ⟨y₀, hy₀, hgy₀⟩ := hzi
      have hyEq : q j y₀ = r j tV := hy₀.trans (neighborhoodStalkMap_closedPoint (h j)).symm
      obtain ⟨zj, hzfst, hzsnd⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := q j) (g := r j) y₀ tV hyEq
      refine ⟨Sigma.ι Z j zj, ?_, ?_⟩
      · change (P ≫ pullback.snd f aV) (Sigma.ι Z j zj) = tV
        have hh : (Sigma.ι Z j ≫ P ≫ pullback.snd f aV) zj = tV := by
          rw [← Category.assoc, Sigma.ι_comp_desc, hpChart_snd]
          exact hzsnd
        simpa only [Scheme.Hom.comp_apply] using hh
      · have hz : f.fiberι s z = z₀ := f.fiberι_fiberHomeo_symm s ⟨z₀, hz₀⟩
        have hh : (Sigma.ι Z j ≫ P ≫ pullback.fst f aV) zj = z₀ := by
          rw [← Category.assoc, Sigma.ι_comp_desc, hpChart_fst]
          simp only [Scheme.Hom.comp_apply, hzfst]
          change (p i ≫ pullback.fst f (aMap j)) y₀ = z₀
          exact hgy₀.trans hz
        simpa only [Scheme.Hom.comp_apply] using hh
    · have hsub := image_closed_fiber_subset f aV
        (P ≫ pullback.fst f aV) (P ≫ pullback.snd f aV) hcomm tV
      have hbase : aV tV = s := neighborhood_closedPoint_over_base V
      rwa [hbase] at hsub
  · intro hqfp
    rw [← hdescQ]
    refine finitePresentation_sigma_desc Z qChart fun i => ?_
    have := (hqfp i.1).1
    infer_instance
  · intro hFfp
    rw [← hdescG]
    refine isFinitePresentation_sigma Z gChart F (fun i => ?_)
    let k : Z i ⟶ Y i.1 := pullback.fst (q i) (r i)
    let g0 : Y i.1 ⟶ X := p i.1 ≫ pullback.fst f (aMap i)
    have hk : k ≫ g0 = gChart i := by
      simpa only [Category.assoc] using (hpChart_fst i).symm
    let e : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g0).obj F) ≅
        (Scheme.Modules.pullback (gChart i)).obj F :=
      (Scheme.Modules.pullbackComp k g0).app F ≪≫ (Scheme.Modules.pullbackCongr hk).app F
    have hG0 : ((Scheme.Modules.pullback g0).obj F).IsFinitePresentation := hFfp i.1
    have hpb : ((Scheme.Modules.pullback k).obj
        ((Scheme.Modules.pullback g0).obj F)).IsFinitePresentation :=
      @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ k.toLRSHom.toShHom
        ((Scheme.Modules.pullback g0).obj F) hG0
    exact (SheafOfModules.isFinitePresentation (Z i).ringCatSheaf).prop_of_iso e hpb
  · rw [← hdescG]
    refine free_globalSections_sigma (.of (V.scheme.presheaf.stalk V.point)) Z gChart F
      (P ≫ pullback.snd f aV) qChart (fun i => ?_) (fun i => ?_)
    · change (Sigma.ι Z i ≫ P) ≫ pullback.snd f aV = pullback.snd (q i) (r i)
      rw [Sigma.ι_comp_desc, hpChart_snd]
    · exact free_sections_pullback_base_change
        (.of ((U i.1).scheme.presheaf.stalk (U i.1).point)) (.of (V.scheme.presheaf.stalk V.point))
        (neighborhoodStalkMap (h i)) (q i) (p i.1 ≫ pullback.fst f (aMap i)) F (gChart i)
        (by simpa only [Category.assoc] using (hpChart_fst i).symm) (hfree i.1)


/-! ### Tag 05L0 -/

/-- **Stacks Project, Tag 05L0.** Let `f : X ⟶ S` be of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `s : S` be such that `F` is flat over `S` at
every point of the fibre `X_s`. Then there are an elementary étale neighbourhood
`(S', s') ⟶ (S, s)` and a commutative diagram
```
  X  ←ᵍ  X'
  ↓      ↓
  S  ←  Spec 𝒪_{S', s'}
```
such that `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `X_s = g((X')_{s'})`, `X'` is affine and of
finite presentation over `𝒪_{S', s'}`, `g^*F` is of finite presentation, and `Γ(X', g^*F)` is a
free `𝒪_{S', s'}`-module.

The inputs are Tag 05KY,
`AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_isFiniteType`, applied at
every point of the fibre, and Tag 057B, which makes the elementary étale neighbourhoods of
`(S, s)` cofiltered so that the finitely many neighbourhoods surviving the quasi-compactness of
the fibre are dominated by one of them. -/
@[stacks 05L0]
theorem exists_elementaryEtaleNeighborhood_free_sections_along_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (hfp : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (X' : Scheme.{u})
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (g : X' ⟶ X)
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : f ⁻¹' {s} = g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  classical
  let : LocallyOfFinitePresentation f := hfp.1
  let : QuasiCompact f := hfp.2.1
  choose U hU Y y p hp hAff hx hy hqfp hFfp hfree using
    fun x => local_chart_at_fiber_point f F s x hflat
  obtain ⟨V, hV, X', q, g, hcomm, het, hcov, haff, hq, hg, hfr⟩ :=
    exists_free_sections_of_charts f F s U hU Y y p hp hAff hx hy hfree
  exact ⟨V, hV, X', q, g, hcomm, het, hcov, haff, hq hqfp, hg hFfp, hfr⟩

/-- **Tag 05L0 with the free module read on the local base.** The conclusion of Tag 05L0 with
its freeness clause replaced by an isomorphism of `𝒪_{Spec 𝒪_{S', s'}}`-modules between the
pushforward of `g^*F` to `Spec 𝒪_{S', s'}` and a free module on an index type.

Everything else in the existential is the conclusion of
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_along_fibre` unchanged. The
two statements say the same thing, `X'` being affine and `g^*F` quasi-coherent; the point of
this form is that no restriction of scalars occurs in it, so it needs no `letI` to be read and
instance resolution finds everything it mentions. -/
theorem exists_elementaryEtaleNeighborhood_free_sheaf_along_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (hfp : FinitePresentation f)
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (X' : Scheme.{u})
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (g : X' ⟶ X)
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : f ⁻¹' {s} = g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation)
      (I : Type u),
      Nonempty ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback g).obj F) ≅
        SheafOfModules.free I) := by
  obtain ⟨U, hU, X', q, g, hcomm, het, hcov, haff, hqfp, hFfp, hfree⟩ :=
    exists_elementaryEtaleNeighborhood_free_sections_along_fibre f F hfp s hflat
  refine ⟨U, hU, X', q, g, hcomm, het, hcov, haff, hqfp, hFfp, ?_⟩
  have : IsAffine X' := haff
  have : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := pullback_isQuasicoherent' g F
  have : IsAffineHom q := inferInstance
  have : ((Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback g).obj F)).IsQuasicoherent := inferInstance
  have : Module.Free (U.scheme.presheaf.stalk U.point)
      Γ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback g).obj F), ⊤) := hfree
  exact free_sheaf_of_free_sections _ _

/-! ### Tag 05L1 -/

/-- **Tag 05KZ in chart form.** At a point of the fibre `X_s` of a morphism locally of finite
type there are an elementary étale neighbourhood `(S', s')` of `(S, s)` and an affine scheme `Y`
étale over `X ×_S Spec 𝒪_{S', s'}` whose chart hits the point over the closed point and carries
free sections of the pullback of `F`. -/
private lemma local_chart_at_fiber_point_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (x : f.fiber s)
    (hflat : ∀ y : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (Y : Scheme.{u}) (y : Y)
      (p : Y ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase))
      (_ : Etale p) (_ : IsAffine Y)
      (_ : (p ≫ pullback.fst f
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y = f.fiberι s x)
      (_ : (p ≫ pullback.snd f
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y =
          IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback
            (p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫
            (p ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback
          (p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F, ⊤) := by
  have hs : f (f.fiberι s x) = s := (f.range_fiberι s).subset (Set.mem_range_self x)
  have h := exists_etale_neighborhood_with_free_globalSections_of_locallyOfFiniteType
    f F (f.fiberι s x) (hflat x)
  rw [hs] at h
  rcases h with ⟨U, hU, Y, y, g, q, hyx, hyq, hcomm, het, hres, hAff, hfree⟩
  let p := pullback.lift g q hcomm
  have hpFst : p ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) = g :=
    pullback.lift_fst _ _ _
  have hpSnd : p ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) = q :=
    pullback.lift_snd _ _ _
  refine ⟨U, hU, Y, y, p, by simpa only [p] using het, hAff, ?_, ?_, ?_⟩
  · rwa [hpFst]
  · rwa [hpSnd]
  · rw [hpFst, hpSnd]
    exact hfree

/-- **Stacks Project, Tag 05L1.** Let `f : X ⟶ S` be of finite type, let `F` be a quasi-coherent
`𝒪_X`-module of finite type and let `s : S` be such that `F` is flat over `S` at every point of
the fibre `X_s`. Then there are an elementary étale neighbourhood `(S', s') ⟶ (S, s)` and a
commutative diagram
```
  X  ←ᵍ  X'
  ↓      ↓
  S  ←  Spec 𝒪_{S', s'}
```
such that `X' ⟶ X ×_S Spec 𝒪_{S', s'}` is étale, `X_s = g((X')_{s'})`, `X'` is affine, and
`Γ(X', g^*F)` is a free `𝒪_{S', s'}`-module.

This differs from Tag 05L0 only in assuming `f` of finite type rather than of finite
presentation, the input at each point of the fibre being Tag 05KZ,
`AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_locallyOfFiniteType`,
in place of Tag 05KY; correspondingly the two finite-presentation clauses are dropped from the
conclusion. -/
@[stacks 05L1]
theorem exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (X' : Scheme.{u})
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (g : X' ⟶ X)
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : f ⁻¹' {s} = g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X'),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  choose U hU Y y p hp hAff hx hy hfree using
    fun x => local_chart_at_fiber_point_of_locallyOfFiniteType f F s x hflat
  obtain ⟨V, hV, X', q, g, hcomm, het, hcov, haff, -, -, hfr⟩ :=
    exists_free_sections_of_charts f F s U hU Y y p hp hAff hx hy hfree
  exact ⟨V, hV, X', q, g, hcomm, het, hcov, haff, hfr⟩

/-- **Tag 05L1 with the free module read on the local base.** The conclusion of Tag 05L1 with
its freeness clause replaced by an isomorphism of `𝒪_{Spec 𝒪_{S', s'}}`-modules between the
pushforward of `g^*F` to `Spec 𝒪_{S', s'}` and a free module on an index type.

This is to
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType`
what `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sheaf_along_fibre` is to
Tag 05L0: the same statement with no restriction of scalars in it. -/
theorem exists_elementaryEtaleNeighborhood_free_sheaf_along_fibre_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (X' : Scheme.{u})
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (g : X' ⟶ X)
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : f ⁻¹' {s} = g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X')
      (I : Type u),
      Nonempty ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback g).obj F) ≅
        SheafOfModules.free I) := by
  obtain ⟨U, hU, X', q, g, hcomm, het, hcov, haff, hfree⟩ :=
    exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType f F s hflat
  refine ⟨U, hU, X', q, g, hcomm, het, hcov, haff, ?_⟩
  have : IsAffine X' := haff
  have : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := pullback_isQuasicoherent' g F
  have : IsAffineHom q := inferInstance
  have : ((Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback g).obj F)).IsQuasicoherent := inferInstance
  have : Module.Free (U.scheme.presheaf.stalk U.point)
      Γ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback g).obj F), ⊤) := hfree
  exact free_sheaf_of_free_sections _ _


/-- **The conclusion of Tag 05L1 pulls back along a morphism of étale neighbourhoods.** Let
`h : (V, v) ⟶ (U, u)` be a morphism of étale neighbourhoods of `s`, and let `X'` be an affine
scheme over `Spec 𝒪_{U, u}` with `X' ⟶ X ×_S Spec 𝒪_{U, u}` étale and `Γ(X', g^*F)` free over
`𝒪_{U, u}`. Then the base change `X'' = X' ×_{Spec 𝒪_{U, u}} Spec 𝒪_{V, v}` has the same three
properties over `Spec 𝒪_{V, v}`, and the image in `X` of its fibre over the closed point is the
image of the fibre of `X'` over the closed point.

This is the step of the proof of Tag 05L1 which passes to a common refinement of finitely many
neighbourhoods, for a single one; it is what allows the neighbourhood that Tag 05L1 produces to
be shrunk, for instance to an affine open neighbourhood of its distinguished point. -/
theorem exists_free_sections_along_fibre_of_neighborhoodHom {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {s : S} {U V : EtaleNeighborhood S s} (h : V ⟶ U)
    {X' : Scheme.{u}} [IsAffine X'] (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
    (g : X' ⟶ X) (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
    (het : Etale (pullback.lift g q hcomm))
    (hfree :
      letI : Module (U.scheme.presheaf.stalk U.point) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point) Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ∃ (X'' : Scheme.{u}) (q' : X'' ⟶ Spec (.of (V.scheme.presheaf.stalk V.point)))
      (g' : X'' ⟶ X) (hcomm' : g' ≫ f = q' ≫ V.scheme.fromSpecStalk V.point ≫ V.toBase)
      (_ : Etale (pullback.lift g' q' hcomm'))
      (_ : g' '' (q' ⁻¹' {IsLocalRing.closedPoint _}) =
        g '' (q ⁻¹' {IsLocalRing.closedPoint _}))
      (_ : IsAffine X''),
      letI : Module (V.scheme.presheaf.stalk V.point)
          Γ((Scheme.Modules.pullback g').obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (V.scheme.presheaf.stalk V.point))).inv ≫ q'.appTop).hom
      Module.Free (V.scheme.presheaf.stalk V.point) Γ((Scheme.Modules.pullback g').obj F, ⊤) := by
  classical
  let aU : Spec (.of (U.scheme.presheaf.stalk U.point)) ⟶ S :=
    U.scheme.fromSpecStalk U.point ≫ U.toBase
  let aV : Spec (.of (V.scheme.presheaf.stalk V.point)) ⟶ S :=
    V.scheme.fromSpecStalk V.point ≫ V.toBase
  let φ := neighborhoodStalkMap h
  let r : Spec (.of (V.scheme.presheaf.stalk V.point)) ⟶
      Spec (.of (U.scheme.presheaf.stalk U.point)) := Spec.map φ
  have hr : r ≫ aU = aV := neighborhoodStalkMap_over_base h
  let p : X' ⟶ pullback f aU := pullback.lift g q hcomm
  have : Etale p := het
  have hq : p ≫ pullback.snd f aU = q := pullback.lift_snd _ _ _
  let Z : Scheme.{u} := pullback q r
  have : IsAffine Z := by dsimp [Z]; infer_instance
  let g' : Z ⟶ X := pullback.fst q r ≫ g
  let q' : Z ⟶ Spec (.of (V.scheme.presheaf.stalk V.point)) := pullback.snd q r
  have hcomm' : g' ≫ f = q' ≫ aV := by
    simp only [g', q', Category.assoc, hcomm, ← hr]
    rw [← Category.assoc (pullback.fst q r), pullback.condition, Category.assoc]
  refine ⟨Z, q', g', hcomm', ?_, ?_, inferInstance, ?_⟩
  · -- the induced morphism is the base change of `p`, up to the identification of bases
    let m : Z ⟶ pullback (pullback.snd f aU) r :=
      pullback.map q r (pullback.snd f aU) r p (𝟙 _) (𝟙 _)
        (by simp [hq]) (by simp)
    have hm : Etale m := etale_pullback_map_chart f aU r p q hq
    have hlift : pullback.lift g' q' hcomm' =
        m ≫ (pullbackLeftPullbackSndIso f aU r).hom ≫ (pullback.congrHom rfl hr).hom := by
      apply pullback.hom_ext
      · simp only [m, g', p, Category.assoc, pullback.lift_fst, pullback.congrHom_hom,
          Category.comp_id]
        rw [pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc, pullback.lift_fst,
          Category.assoc, pullback.lift_fst]
      · simp only [m, q', Category.assoc, pullback.lift_snd, pullback.congrHom_hom,
          Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
    rw [hlift]
    exact MorphismProperty.comp_mem @Etale _ _ hm
      (MorphismProperty.comp_mem @Etale _ _ inferInstance inferInstance)
  · let tV := IsLocalRing.closedPoint (V.scheme.presheaf.stalk V.point)
    have hclosed : r tV = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) :=
      neighborhoodStalkMap_closedPoint h
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨pullback.fst q r z, ?_, rfl⟩
      change q (pullback.fst q r z) = _
      have h1 : q (pullback.fst q r z) = r (pullback.snd q r z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      rw [h1]
      have hz' : pullback.snd q r z = tV := hz
      rw [hz', hclosed]
    · rintro _ ⟨y₀, hy₀, rfl⟩
      have hyEq : q y₀ = r tV := hy₀.trans hclosed.symm
      obtain ⟨z, hzfst, hzsnd⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := q) (g := r) y₀ tV hyEq
      exact ⟨z, hzsnd, by simp only [g', Scheme.Hom.comp_apply, hzfst]⟩
  · exact free_sections_pullback_base_change (.of (U.scheme.presheaf.stalk U.point))
      (.of (V.scheme.presheaf.stalk V.point)) φ q g F g' rfl hfree

end AlgebraicGeometry

end
