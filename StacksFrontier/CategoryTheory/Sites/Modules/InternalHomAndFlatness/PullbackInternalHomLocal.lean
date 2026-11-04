module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomFlat
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The objects over which a finitely presented sheaf of modules is globally presented

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, and let `F` be a sheaf of `O_D`-modules of finite presentation in the sense of
Tag 03DL — every object of `D` has a covering on whose members `F` admits a finite global
presentation. The images `u(V)` of the objects `V` of `D` over which `F` admits a finite global
presentation cover the final object of `Sh(C)`. For `F` admitting a finite global presentation
over the whole of `D`, the canonical map `f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)` of
Stacks 0GMX is an isomorphism when `f` is flat.

## Main results

* `Stacks.SheafOfModules.InternalHom.coversTop_obj_hasFiniteGlobalPresentation`: for a sheaf of
  modules of finite presentation in the sense of Tag 03DL, the images under `u` of the objects
  of `D` over which it admits a finite global presentation cover the final object of `Sh(C)`.
* `Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation`:
  **Stacks 0GN2 for an `F` admitting a finite global presentation**, the presentation being
  assumed as the property `SheafOfModules.HasFiniteGlobalPresentation`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u

section Covering

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The objects over which a finitely presented sheaf of modules is globally presented cover
the source site.** Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites with underlying
continuous functor `u : D ⥤ C`, and let `F` be a sheaf of `O_D`-modules of finite presentation
in the sense of Tag 03DL. Then the family of objects `u(V)` of `C`, indexed by those objects `V`
of `D` on which `F` admits a finite global presentation, covers the final object of `Sh(C)`. -/
@[ega "0 6.7.6" "Localization step"]
theorem coversTop_obj_hasFiniteGlobalPresentation [F.IsFinitePresentationOnSite] :
    X.J.CoversTop (fun V : {V : Y.C //
        _root_.SheafOfModules.HasFiniteGlobalPresentation (F.over V)} => f.u.obj V.val) := by
  have : Limits.PreservesFiniteLimits (f.u.sheafPullback (Type u) Y.J X.J) :=
    f.isMorphismOfSites.preservesFiniteLimits
  have : Limits.PreservesLimit (Functor.empty.{0} (Sheaf Y.J (Type u)))
      (f.u.sheafPullback (Type u) Y.J X.J) := inferInstance
  have hTop : X.J.CoversTop f.u.obj :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback
      f.u Y.J X.J
  refine CategoryTheory.GrothendieckTopology.coversTop_obj_subtype f.u Y.J X.J hTop _
    (fun U => ?_)
  obtain ⟨I, V, g, hg, h⟩ :=
    _root_.SheafOfModules.IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation
      (F := F) U
  exact ⟨Presieve.ofArrows V g, hg, by rintro W k ⟨i⟩; exact h i⟩

section GlobalPresentationAsAProperty

variable (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- A sheaf of modules whose sections already lie in the universe in which the coproducts of a
global presentation are formed is isomorphic to its universe lift. -/
private noncomputable def uliftSelf
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    M ≅ _root_.SheafOfModules.uliftForPresentation.{u, u, u, u, u} M :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun Z ↦ (ULift.moduleEquiv
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj Z)
        (M := M.val.obj Z)).symm.toModuleIso) (by
        intro Z Z' h
        ext x
        rfl))

/-- A finite coproduct of copies of `A'` is a finite coproduct of copies of any `A` isomorphic
to `A'`. -/
private noncomputable def isColimitCofanComp {n : ℕ} {A A' P : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (e : A ≅ A') (ι : Fin n → (A' ⟶ P))
    (hP : Limits.IsColimit (Limits.Cofan.mk P ι)) :
    Limits.IsColimit (Limits.Cofan.mk P (fun i ↦ e.hom ≫ ι i)) :=
  Limits.Cofan.IsColimit.mk _
    (fun t ↦ hP.desc (Limits.Cofan.mk t.pt (fun i ↦ e.inv ≫ t.inj i)))
    (fun t i ↦ by
      have := hP.fac (Limits.Cofan.mk t.pt (fun i ↦ e.inv ≫ t.inj i)) ⟨i⟩
      simp only [Limits.Cofan.mk_pt, Limits.Cofan.inj, Limits.Cofan.mk_ι_app] at this ⊢
      rw [Category.assoc, this, ← Category.assoc, e.hom_inv_id, Category.id_comp])
    (fun t m hm ↦ by
      refine hP.uniq (Limits.Cofan.mk t.pt (fun i ↦ e.inv ≫ t.inj i)) m (fun j ↦ ?_)
      obtain ⟨i⟩ := j
      have h := hm i
      simp only [Limits.Cofan.mk_pt, Limits.Cofan.inj, Limits.Cofan.mk_ι_app,
        Category.assoc] at h ⊢
      rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp])

/-- **Stacks 0GN2 for an `F` admitting a finite global presentation.** Let
`f : (C, O_C) ⟶ (D, O_D)` be a flat morphism of ringed sites and let `F`, `G` be sheaves of
`O_D`-modules with `F` admitting, over the whole site `D`, a presentation as the cokernel of a
morphism between finite coproducts of copies of `O_D`. Then the canonical map
`f^* Hom_{O_D}(F, G) ⟶ Hom_{O_C}(f^*F, f^*G)` of Stacks 0GMX is an isomorphism. -/
@[sga "3 III 0.6" "special case"]
theorem isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage)
    (hF : _root_.SheafOfModules.HasFiniteGlobalPresentation F) :
    IsIso (pullbackInternalHomMap f F G) := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hF
  refine isIso_pullbackInternalHomMap f G F hf
    (fun i ↦ (uliftSelf _).hom ≫ ι i) (fun i ↦ (uliftSelf _).hom ≫ κ i)
    (isColimitCofanComp _ _ hP) (isColimitCofanComp _ _ hQ)
    a (b ≫ (uliftSelf F).inv) ?_ ?_
  · rw [← Category.assoc, hab, Limits.zero_comp]
  · exact Limits.IsColimit.ofIsoColimit hb (Limits.Cofork.ext (uliftSelf F).symm rfl)

end GlobalPresentationAsAProperty

end Covering

end Stacks.SheafOfModules.InternalHom

end
