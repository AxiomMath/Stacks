module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSupport
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of the pullback of a module of finite type

For a morphism of schemes `f : Y ⟶ X` and an `𝒪_X`-module `F` of finite type, the support of
`f^* F` is the inverse image of the support of `F`. The proof compares the two stalks through
skyscraper modules rather than through a stalk formula for `f^*`: by the adjunction between the
stalk functor and the skyscraper functor, by the pullback–pushforward adjunction, and by the
identification of `f_*` of a skyscraper at `y` with the skyscraper at `f y`, the two sets

`Hom_{𝒪_{Y,y}}((f^* F)_y, V)` and `Hom_{𝒪_{X,f y}}(F_{f y}, V)`

are in bijection for every `𝒪_{Y,y}`-module `V`, `V` being regarded as an `𝒪_{X,f y}`-module by
restriction of scalars along the stalk map. Nonvanishing of each stalk is then read off that
bijection.

## Main definitions

* `Stacks.Modules.schemeSkyscraper` is the skyscraper `𝒪_X`-module at a point of a scheme.
* `Stacks.Modules.pushforwardSkyscraperIso` identifies the pushforward of a skyscraper with a
  skyscraper, and `Stacks.Modules.pushforwardSkyscraperNatIso` is its functorial form.

## Main results

* `Stacks.Modules.supp_pullback` computes the support of a pullback.

## Implementation notes

The bijection is used only to transport `Nontrivial` and `Subsingleton`, so no naturality of it
is needed here; the adjunctions themselves are in
`StacksFrontier.Topology.Sheaves.Skyscraper.Modules`. The hard direction uses the local-algebra
input `Stacks.Support.exists_surjective_toResidueField` together with
`SheafOfModules.finite_stalk`: a nonzero finite module over a local ring surjects onto the
residue field, and the residue field of `𝒪_{X,f y}` maps to that of `𝒪_{Y,y}` because the stalk
map is local. That produces a nonzero `𝒪_{X,f y}`-linear map out of `F_{f y}`, hence a nonzero
`𝒪_{Y,y}`-linear map out of `(f^* F)_y`.

The module structure on a stalk is supplied by `let`-bound instances spelled exactly as in
`StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSupport`, because instance search does
not find Mathlib's instance for a sheaf of modules over `(sheafCompose _ (forget₂ _ _)).obj R`.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Limits AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {X Y : Scheme.{u}}

/-- The skyscraper `𝒪_X`-module at a point `z` of a scheme `X` with value the
`𝒪_{X,z}`-module `V`. -/
noncomputable def schemeSkyscraper (z : X) (V : ModuleCat.{u} ↑(X.presheaf.stalk z)) :
    X.Modules :=
  skyscraper X.sheaf z V

/-- The pushforward of a skyscraper along a morphism of schemes is the skyscraper at the image
point, with its value restricted along the induced map of local rings. On sections this is the
identity: the opens match because `y ∈ f⁻¹ U` and `f y ∈ U` are the same proposition, and the
two `𝒪_X(U)`-actions agree by the compatibility of germs with the stalk map. -/
noncomputable def pushforwardSkyscraperIso (f : Y ⟶ X) (y : Y)
    (V : ModuleCat.{u} ↑(Y.presheaf.stalk y)) :
    (Scheme.Modules.pushforward f).obj (schemeSkyscraper y V) ≅
      schemeSkyscraper (f y) ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj V) where
  hom := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g : PLift (y ∈ f ⁻¹ᵁ U.unop) → ↑V => fun h => g ⟨h.down⟩)
          (fun _ _ => rfl))
      naturality := by intros; rfl }
    (fun U r m => funext fun h =>
      congrArg (fun a => a • m ⟨h.down⟩)
        (f.germ_stalkMap_apply U.unop y h.down r).symm)⟩
  inv := ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g : PLift (f y ∈ U.unop) → ↑V => fun h => g ⟨h.down⟩)
          (fun _ _ => rfl))
      naturality := by intros; rfl }
    (fun U r m => funext fun h =>
      congrArg (fun a => a • m ⟨h.down⟩)
        (f.germ_stalkMap_apply U.unop y h.down r))⟩
  hom_inv_id := Scheme.Modules.hom_ext _ _ fun _ => rfl
  inv_hom_id := Scheme.Modules.hom_ext _ _ fun _ => rfl

/-- `Stacks.Modules.pushforwardSkyscraperIso` is natural in the value: pushing a skyscraper
forward along `f` is, as a functor of the value, restriction of scalars along the stalk map
followed by the skyscraper at the image point. -/
noncomputable def pushforwardSkyscraperNatIso (f : Y ⟶ X) (y : Y) :
    skyscraperFunctor Y.sheaf y ⋙ Scheme.Modules.pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap y).hom ⋙ skyscraperFunctor X.sheaf (f y) :=
  NatIso.ofComponents (fun V => pushforwardSkyscraperIso f y V)
    (fun _ => Scheme.Modules.hom_ext _ _ fun _ => rfl)

/-! ### Two elementary facts about modules of linear maps -/

/-- Linear maps out of a zero module form a singleton. -/
lemma subsingleton_linearMap {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Subsingleton M] : Subsingleton (M →ₗ[R] N) :=
  ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩

/-- A module whose linear endomorphisms form a singleton is zero. -/
lemma subsingleton_of_subsingleton_endLinearMap {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (h : Subsingleton (M →ₗ[R] M)) : Subsingleton M := by
  have hid : (LinearMap.id : M →ₗ[R] M) = 0 := h.elim _ _
  have h0 : ∀ a : M, a = 0 := fun a => by simpa using LinearMap.congr_fun hid a
  exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩

/-- `ResidueField S`, viewed as a module over `R` by restriction of scalars along a local
homomorphism `g : R →+* S`, receives `ResidueField R` `R`-linearly through
`IsLocalRing.ResidueField.map`. -/
noncomputable def residueFieldMapRestrict {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (g : R →+* S) [IsLocalHom g] :
    IsLocalRing.ResidueField R →ₗ[R]
      ↑((ModuleCat.restrictScalars g).obj (ModuleCat.of S (IsLocalRing.ResidueField S))) where
  toFun := IsLocalRing.ResidueField.map g
  map_add' := map_add _
  map_smul' a c := by
    change IsLocalRing.ResidueField.map g (a • c) = _
    rw [Algebra.smul_def,
      show algebraMap R (IsLocalRing.ResidueField R) a = IsLocalRing.residue R a from rfl,
      map_mul, IsLocalRing.ResidueField.map_residue]
    exact (Algebra.smul_def (g a) _).symm

/-! ### The support of a pullback -/

/-- **Stacks 056J.** The support of the pullback of an `𝒪_X`-module of finite type along a
morphism of schemes is the inverse image of its support. -/
theorem supp_pullback (f : Y ⟶ X) (F : X.Modules) [F.IsFiniteType] :
    SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) =
      f ⁻¹' SheafOfModules.supp F := by
  ext y
  simp only [Set.mem_preimage]
  refine Iff.trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk ((Scheme.Modules.pullback f).obj F) y)
    (Iff.trans ?_ (SheafOfModules.mem_supp_iff_nontrivial_stalk F (f y)).symm)
  change Nontrivial ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj F).val.presheaf y) ↔
    Nontrivial ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))
  let : Module ↑(X.presheaf.stalk (f y)) ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f y)
  let : Module ↑(Y.presheaf.stalk y)
      ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj F).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.pullback f).obj F).val y
  have key : ∀ V : ModuleCat.{u} ↑(Y.presheaf.stalk y),
      (↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj F).val.presheaf y) →ₗ[
          ↑(Y.presheaf.stalk y)] ↑V) ≃
        (↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) →ₗ[↑(X.presheaf.stalk (f y))]
          ↑((ModuleCat.restrictScalars (f.stalkMap y).hom).obj V)) := fun V =>
    (skyscraperHomEquiv Y.sheaf y V ((Scheme.Modules.pullback f).obj F)).symm.trans
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F (schemeSkyscraper y V)).trans
        (((Iso.refl F).homCongr (pushforwardSkyscraperIso f y V)).trans
          (skyscraperHomEquiv X.sheaf (f y) _ F)))
  constructor
  · intro hpb
    by_contra hc
    have : Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) :=
      not_nontrivial_iff_subsingleton.mp hc
    refine absurd (subsingleton_of_subsingleton_endLinearMap
        (R := ↑(Y.presheaf.stalk y)) ?_)
      (not_subsingleton_iff_nontrivial.mpr hpb)
    exact (key (ModuleCat.of ↑(Y.presheaf.stalk y)
        ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj F).val.presheaf
          y))).subsingleton_congr.mpr subsingleton_linearMap
  · intro hF
    have : Module.Finite ↑(X.presheaf.stalk (f y))
        ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) :=
      SheafOfModules.finite_stalk X.sheaf F (f y)
    obtain ⟨φ, hφ⟩ := Stacks.Support.exists_surjective_toResidueField
      (R := ↑(X.presheaf.stalk (f y))) (M := ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)))
    set V : ModuleCat.{u} ↑(Y.presheaf.stalk y) :=
      ModuleCat.of ↑(Y.presheaf.stalk y) (IsLocalRing.ResidueField ↑(Y.presheaf.stalk y))
    have hne : (residueFieldMapRestrict (f.stalkMap y).hom).comp φ ≠ 0 := fun h0 => by
      obtain ⟨m, hm⟩ := hφ 1
      have : IsLocalRing.ResidueField.map (f.stalkMap y).hom (1 : _) = 0 :=
        hm ▸ LinearMap.congr_fun h0 m
      exact one_ne_zero ((map_one _).symm.trans this)
    have hnt : Nontrivial (↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) →ₗ[
        ↑(X.presheaf.stalk (f y))] ↑((ModuleCat.restrictScalars (f.stalkMap y).hom).obj V)) :=
      ⟨_, _, hne⟩
    by_contra hc
    have : Subsingleton
        ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback f).obj F).val.presheaf y) :=
      not_nontrivial_iff_subsingleton.mp hc
    exact (not_subsingleton_iff_nontrivial.mpr ((key V).nontrivial_congr.mpr hnt))
      subsingleton_linearMap

end Stacks.Modules

end
