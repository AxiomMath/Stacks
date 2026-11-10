module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimitUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Local injectivity of the colimit model of the pullback, along a locally flat morphism

Let `F : C ⥤ D` be a functor, `S` and `R` presheaves of commutative rings on `C` and `D`, and
`ψ : S ⟶ F.op ⋙ R` a morphism of presheaves of rings.  The pullback of presheaves of modules
along `ψ` is objectwise extension of scalars along `ψ`
(`Stacks.NoncommChangeOfRings.Presheaf.extendScalars`) followed by the objectwise colimit `L₀` of
`Stacks.PullbackColimitUnivLE`, whose sections over `U` are

`colim_{(V, U ⟶ F V)} R(U) ⊗_{R(F V)} (R(F V) ⊗_{S(V)} M(V))`.

When the index categories are filtered and, locally on every `U`, every index is dominated by
one at which the composite ring map `S(V) ⟶ R(F V) ⟶ R(U)` is flat, this composite carries a
sectionwise injective morphism of presheaves of modules to a **locally injective** one.  This is
the argument by which the inverse image of modules along a flat morphism of ringed sites is left
exact: a section in the kernel comes from a single index, dies at a later index, and dies at once
after restriction to the members of a covering over which the indices are flat, because there the
term of the colimit is a base change along a flat ring map.

## Main results

* `Stacks.PullbackColimitUnivLE.injective_extendScalars_map_noncommExtendScalars_map`: base change
  along a composite `A ⟶ B ⟶ C` of ring maps whose composite is flat preserves injectivity.
* `Stacks.PullbackColimitUnivLE.colimitPullback_map_app_ι`: `L₀` on a morphism, on the image of a
  term of the colimit.
* `Stacks.PullbackColimitUnivLE.isLocallyInjective_colimitPullback_map_extendScalars_map`: the
  local injectivity statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe r v₁ v₂ u₁ u₂

namespace Stacks.PullbackColimitUnivLE

open PresheafOfModules

/-- **Base change along a composite with flat composite preserves injectivity.**  For ring maps
`f : A ⟶ B` and `g : B ⟶ C` with `g ∘ f` flat, the base change along `g` of the base change along
`f` of an injective linear map is injective: the composite base change is left adjoint to the
composite restriction of scalars, hence is base change along `g ∘ f`. -/
theorem injective_extendScalars_map_noncommExtendScalars_map {A B C : Type r} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (hgf : (g.comp f).Flat)
    {M N : ModuleCat.{r + 1} A} (i : M ⟶ N) (hi : Function.Injective i) :
    Function.Injective ((ModuleCat.extendScalars.{r, r, r + 1} g).map
      ((Stacks.NoncommChangeOfRings.extendScalars.{r + 1} f).map i)) := by
  let adj := (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{r + 1} f).comp
    (ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} g)
  let adj' : ModuleCat.extendScalars.{r, r, r + 1} (g.comp f) ⊣
      ModuleCat.restrictScalars.{r + 1} g ⋙ ModuleCat.restrictScalars.{r + 1} f :=
    (ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} (g.comp f)).ofNatIsoRight
      (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl)
  let e := adj.leftAdjointUniq adj'
  have hlex : PreservesFiniteLimits (ModuleCat.extendScalars.{r, r, r + 1} (g.comp f)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{r, r + 1} (g.comp f) hgf
  have hpm : (ModuleCat.extendScalars.{r, r, r + 1} (g.comp f)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have hmono : Mono ((ModuleCat.extendScalars.{r, r, r + 1} (g.comp f)).map i) :=
    @Functor.map_mono _ _ _ _ _ hpm _ _ i ((ModuleCat.mono_iff_injective i).2 hi)
  have heq : (ModuleCat.extendScalars.{r, r, r + 1} g).map
      ((Stacks.NoncommChangeOfRings.extendScalars.{r + 1} f).map i) =
        e.hom.app M ≫ (ModuleCat.extendScalars.{r, r, r + 1} (g.comp f)).map i ≫ e.inv.app N := by
    rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  rw [heq]
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r}) [UnivLE.{max u₁ v₂, r + 1}]

/-- **`L₀` on a morphism, on the image of a term of the colimit**: it is the base change of the
component of the morphism. -/
lemma colimitPullback_map_app_ι
    {A A' : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (f : A ⟶ A') {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (y : diagramObj F R A T) :
    Hom.app ((colimitPullback F R).map f) U (colimit.ι (diagram F R A U) T y) =
      colimit.ι (diagram F R A' U) T
        ((ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).map (Hom.app f T.left) y) := by
  have key : colimit.ι (diagram F R A U) T ≫ Hom.app ((colimitPullback F R).map f) U =
      (ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).map (Hom.app f T.left) ≫
        colimit.ι (diagram F R A' U) T := by
    refine extendScalars_hom_ext _ fun a => ?_
    change descMap F R (f ≫ toPushforward F R (𝟙 _)) U (germ F R A T 1 a) =
      germ F R A' T 1 (Hom.app f T.left a)
    rw [descMap_germ]
    exact (germ_one_eq_map_unit F R (A := A') T.hom (Hom.app f T.left a)).symm
  exact ConcreteCategory.congr_hom key y

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- The transition maps of the colimit are natural in the module. -/
lemma diagramMap_extendScalars_map
    {A A' : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (f : A ⟶ A') {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (χ : T ⟶ T')
    (y : diagramObj F R A T) :
    diagramMap F R A' χ
        ((ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).map (Hom.app f T.left) y) =
      (ModuleCat.extendScalars.{r, r, r + 1} (R.map T'.hom).hom).map (Hom.app f T'.left)
        (diagramMap F R A χ y) := by
  have key : (ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).map (Hom.app f T.left) ≫
      diagramMap F R A' χ = diagramMap F R A χ ≫
        (ModuleCat.extendScalars.{r, r, r + 1} (R.map T'.hom).hom).map (Hom.app f T'.left) := by
    refine extendScalars_hom_ext _ fun a => ?_
    change tmul (R.map T'.hom).hom 1 (A'.map χ.left (Hom.app f T.left a)) =
      tmul (R.map T'.hom).hom 1 (Hom.app f T'.left (A.map χ.left a))
    rw [naturality_apply]
  exact ConcreteCategory.congr_hom key y

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- The restriction maps of the colimit, on the terms, are natural in the module. -/
lemma baseChangeMap_extendScalars_map
    {A A' : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (f : A ⟶ A') {U U' : Dᵒᵖ} (g : U ⟶ U') {V : Cᵒᵖ} (h : F.op.obj V ⟶ U)
    (h' : F.op.obj V ⟶ U') (hα : ∀ a, (R.map g).hom ((R.map h).hom a) = (R.map h').hom a)
    (y : (ModuleCat.extendScalars.{r, r, r + 1} (R.map h).hom).obj (A.obj V)) :
    baseChangeMap (R.map h).hom (R.map h').hom (σ := (R.map g).hom) (ρ := RingHom.id _) hα
        LinearMap.id ((ModuleCat.extendScalars.{r, r, r + 1} (R.map h).hom).map (Hom.app f V) y) =
      (ModuleCat.extendScalars.{r, r, r + 1} (R.map h').hom).map (Hom.app f V)
        (baseChangeMap (R.map h).hom (R.map h').hom (σ := (R.map g).hom) (ρ := RingHom.id _) hα
          LinearMap.id y) := by
  have key : (ModuleCat.extendScalars.{r, r, r + 1} (R.map h).hom).map (Hom.app f V) ≫
      baseChangeMap (R.map h).hom (R.map h').hom (σ := (R.map g).hom) (ρ := RingHom.id _) hα
        LinearMap.id =
      baseChangeMap (R.map h).hom (R.map h').hom (σ := (R.map g).hom) (ρ := RingHom.id _) hα
          LinearMap.id ≫
        (ModuleCat.restrictScalars (R.map g).hom).map
          ((ModuleCat.extendScalars.{r, r, r + 1} (R.map h').hom).map (Hom.app f V)) :=
    extendScalars_hom_ext _ fun _ => rfl
  exact ConcreteCategory.congr_hom key y

variable {S : Cᵒᵖ ⥤ CommRingCat.{r}} (ψ : S ⟶ F.op ⋙ R)

/-- **The colimit model of the pullback along a locally flat morphism is locally injective on
injective morphisms.**  Let `ψ : S ⟶ F.op ⋙ R` be a morphism of presheaves of commutative rings
whose index categories `CostructuredArrow F.op U` are filtered, and suppose that for every object
`U` of `D` and every index `T = (V, U ⟶ F V)` the arrows `g : U' ⟶ U` along which the restricted
index is dominated by an index `T'` with flat composite ring map `S(V') ⟶ R(F V') ⟶ R(U')`
generate a covering sieve.  Then extension of scalars along `ψ` followed by the objectwise colimit
carries a sectionwise injective morphism to a locally injective one. -/
theorem isLocallyInjective_colimitPullback_map_extendScalars_map
    (J : GrothendieckTopology D) [UnivLE.{v₁, r + 1}]
    [∀ U : Dᵒᵖ, IsFiltered (CostructuredArrow F.op U)]
    (hloc : ∀ (U : D) (T : CostructuredArrow F.op (op U)),
      Sieve.generate (fun U' (g : U' ⟶ U) => ∃ (T' : CostructuredArrow F.op (op U'))
        (_ : CostructuredArrow.mk (T.hom ≫ g.op) ⟶ T'),
          ((R.map T'.hom).hom.comp (ψ.app T'.left).hom).Flat) ∈ J U)
    {K M : PresheafOfModules.{r + 1} (S ⋙ forget₂ CommRingCat RingCat)} (i : K ⟶ M)
    (hi : ∀ V, Function.Injective (Hom.app i V)) :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map ((colimitPullback F R).map
      ((NoncommChangeOfRings.Presheaf.extendScalars.{r + 1}
        (Functor.whiskerRight ψ (forget₂ CommRingCat RingCat))).map i))) := by
  classical
  let E := NoncommChangeOfRings.Presheaf.extendScalars.{r + 1}
    (Functor.whiskerRight ψ (forget₂ CommRingCat RingCat))
  let L := colimitPullback F R
  have hinj : ∀ {U : Dᵒᵖ} (T : CostructuredArrow F.op U),
      ((R.map T.hom).hom.comp (ψ.app T.left).hom).Flat →
      Function.Injective ((ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).map
        (Hom.app (E.map i) T.left)) := fun T hT =>
    injective_extendScalars_map_noncommExtendScalars_map _ _ hT _ (hi T.left)
  refine ⟨fun {U} x₀ y₀ hxy => ?_⟩
  let x : (L.obj (E.obj K)).obj U := x₀
  let y : (L.obj (E.obj K)).obj U := y₀
  have hz : Hom.app (L.map (E.map i)) U (x - y) = 0 := by
    rwa [map_sub, sub_eq_zero]
  have := preservesColimit_diagram F R (E.obj K) U
  have := preservesColimit_diagram F R (E.obj M) U
  obtain ⟨T, w, hw⟩ := exists_ι_eq F R (E.obj K) (x - y)
  rw [← hw, colimitPullback_map_app_ι] at hz
  obtain ⟨T₁, χ, hχ⟩ := exists_map_eq_zero_of_ι_eq_zero F R (E.obj M) _ hz
  rw [diagramMap_extendScalars_map] at hχ
  set w₁ := diagramMap F R (E.obj K) χ w with hw₁
  have hxy' : colimit.ι (diagram F R (E.obj K) U) T₁ w₁ = x - y := by
    rw [← hw, hw₁]
    exact ConcreteCategory.congr_hom (colimit.w (diagram F R (E.obj K) U) χ) w
  refine J.superset_covering ?_ (hloc U.unop T₁)
  rw [Sieve.generate_le_iff]
  rintro U' g ⟨T', χ', hflat⟩
  change (L.obj (E.obj K)).map g.op x = (L.obj (E.obj K)).map g.op y
  rw [← sub_eq_zero, ← map_sub, ← hxy']
  have h1 := obj_map_ι_mk F R (E.obj K) g.op (V := T₁.left) T₁.hom (T₁.hom ≫ g.op) rfl w₁
  change (obj F R (E.obj K)).map g.op (colimit.ι (diagram F R (E.obj K) U) T₁ w₁) = 0
  refine h1.trans ?_
  have hα : ∀ a, (R.map g.op).hom ((R.map T₁.hom).hom a) = (R.map (T₁.hom ≫ g.op)).hom a :=
    fun a ↦ by rw [R.map_comp]; rfl
  let w₂ : diagramObj F R (E.obj K) (CostructuredArrow.mk (T₁.hom ≫ g.op)) :=
    baseChangeMap (R.map T₁.hom).hom (R.map (T₁.hom ≫ g.op)).hom (σ := (R.map g.op).hom)
      (ρ := RingHom.id _) hα LinearMap.id w₁
  change _ = (0 : (obj F R (E.obj K)).obj (op U'))
  change colimit.ι (diagram F R (E.obj K) (op U')) (CostructuredArrow.mk (T₁.hom ≫ g.op)) w₂ = 0
  have h2 : colimit.ι (diagram F R (E.obj K) (op U')) (CostructuredArrow.mk (T₁.hom ≫ g.op)) w₂ =
      colimit.ι (diagram F R (E.obj K) (op U')) T' (diagramMap F R (E.obj K) χ' w₂) :=
    (ConcreteCategory.congr_hom (colimit.w (diagram F R (E.obj K) (op U')) χ') w₂).symm
  rw [h2]
  have h3 : diagramMap F R (E.obj K) χ' w₂ = 0 := by
    refine hinj T' hflat ?_
    have h4 := baseChangeMap_extendScalars_map F R (E.map i) g.op T₁.hom _ hα w₁
    rw [hχ, map_zero] at h4
    rw [map_zero, ← diagramMap_extendScalars_map]
    exact (congrArg _ h4.symm).trans (map_zero _)
  rw [h3]
  exact map_zero _

end Stacks.PullbackColimitUnivLE

end
