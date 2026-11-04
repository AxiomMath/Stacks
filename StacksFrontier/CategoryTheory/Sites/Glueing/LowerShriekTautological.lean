module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekNaturality

/-!
# The `prod.fst` component of Stacks 03EE is the tautological section

Let `(C, J)` be a small site and `U` an object of `C`. Stacks 03EE identifies `j_{U!}j_U^{-1}F`
with `h_U^# × F` (`CategoryTheory.OverShriek.overShriekOverPullbackNatIso`), and a map into a
binary product is its two projections. The projection onto `F` is the counit of
`j_{U!} ⊣ j_U^{-1}`, which is
`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd`. This file computes the
other one.

The projection onto `h_U^#` is *not* a counit: tracing it back through the chain of Stacks 03EE
gives `CategoryTheory.OverShriek.prodSnd`, the map `(φ, s) ↦ φ` of the Stacks 03CD presheaf,
which remembers only the index. What it is instead is the adjunct, under `j_{U!} ⊣ j_U^{-1}`, of
the *tautological section* of `h_U^#` over the localized site: the section of `j_U^{-1}h_U^#`
which over the object `V →φ U` of `C/U` is `φ` itself.

## Main definitions

* `CategoryTheory.OverShriek.tautologicalSection`: for a sheaf `W` on `C/U`, the map
  `W ⟶ j_U^{-1}h_U^#` sending every section over `V →φ U` to the image of `φ` under the
  sheafification unit.

## Main results

* `Stacks.CategoryTheory.homEquiv_map_comp_counit`: the triangle identity in the form that
  recognises a map built as `F.map σ ≫ counit` as the adjunct of `σ`.
* `Stacks.CategoryTheory.leftAdjointUniq_hom_app_comp_of_unit`: for a comparison of two left
  adjoints of one functor, the first of which is a composite `F₁ ⋙ H` of two left adjoints, a map
  out of the second left adjoint is carried by the comparison to the adjunct of a map `σ` as soon
  as the units say so.
* `CategoryTheory.OverShriek.comp_tautologicalSection`: the tautological section is constant,
  i.e. precomposing it with any map of sheaves on `C/U` gives the tautological section again.
* `CategoryTheory.OverShriek.sheafifyNatIso_hom_app_comp_prodSnd`: Stacks 03CD followed by the
  sheafification of `prodSnd` is the adjunct of the tautological section.
* `CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst`: the `prod.fst`
  component of Stacks 03EE is the adjunct of the tautological section.

## References

* [Stacks Project, Tag 03EE](https://stacks.math.columbia.edu/tag/03EE)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.CategoryTheory

open CategoryTheory

variable {A : Type u₁} {B : Type u₂} {D : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D]
  {F₁ : A ⥤ B} {G₁ : B ⥤ A} {H : B ⥤ D} {I : D ⥤ B} {L : A ⥤ D}

/-- **The adjunct of the adjunct.** The transpose, under `adj : F ⊣ G`, of `σ : X ⟶ G.obj Y`
pushed through `F` and followed by the counit, is `σ` again. -/
theorem homEquiv_map_comp_counit {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {X : A} {Y : B}
    (σ : X ⟶ G.obj Y) : adj.homEquiv X Y (F.map σ ≫ adj.counit.app Y) = σ := by
  rw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]

/-- **Uniqueness of a left adjoint, read on the unit side.** Let `adj₁ : F₁ ⊣ G₁` and
`adj₂ : H ⊣ I`, so that `F₁ ⋙ H` is left adjoint to `I ⋙ G₁`, and let `adjB : L ⊣ I ⋙ G₁` be a
second adjunction with the same right adjoint. Given `c : L.obj P ⟶ Y` and
`σ : F₁.obj P ⟶ I.obj Y` whose adjuncts under `adjB` and `adj₁` agree, the canonical comparison
`F₁ ⋙ H ≅ L` carries `c` to the adjunct of `σ` under `adj₂`. -/
theorem leftAdjointUniq_hom_app_comp_of_unit (adj₁ : F₁ ⊣ G₁) (adj₂ : H ⊣ I)
    (adjB : L ⊣ I ⋙ G₁) (P : A) (Y : D) (c : L.obj P ⟶ Y) (σ : F₁.obj P ⟶ I.obj Y)
    (h : adjB.unit.app P ≫ (I ⋙ G₁).map c = adj₁.unit.app P ≫ G₁.map σ) :
    (Adjunction.leftAdjointUniq (adj₁.comp adj₂) adjB).hom.app P ≫ c =
      H.map σ ≫ adj₂.counit.app Y := by
  have key : adj₂.unit.app (F₁.obj P) ≫ I.map (H.map σ ≫ adj₂.counit.app Y) = σ :=
    (Adjunction.homEquiv_unit adj₂ (F₁.obj P) Y
        (H.map σ ≫ adj₂.counit.app Y)).symm.trans (homEquiv_map_comp_counit adj₂ σ)
  refine (((adj₁.comp adj₂).homEquiv P Y).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, h, Adjunction.comp_unit_app, Category.assoc,
    Functor.comp_map, ← Functor.map_comp, key]

end Stacks.CategoryTheory

namespace CategoryTheory.OverShriek

variable {C : Type u} [SmallCategory C] (U : C) (J : GrothendieckTopology C)

/-- **The tautological section of `h_U^#` over the localized site.** For a sheaf `W` on `C/U` the
map `W ⟶ j_U^{-1}h_U^#` which over the object `V →φ U` of `C/U` sends every section of `W` to the
image of `φ` under the sheafification unit of `h_U`. -/
def tautologicalSection (W : Sheaf (J.over U) (Type u)) :
    W ⟶ (localizationPullback U J).obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) :=
  ObjectProperty.homMk
    { app := fun A => ↾fun _ =>
        ((sheafificationAdjunction J (Type u)).unit.app (yoneda.obj U)).app
          (op A.unop.left) A.unop.hom
      naturality := fun {A B} h => by
        ext w
        exact ((congrArg
            (((sheafificationAdjunction J (Type u)).unit.app (yoneda.obj U)).app
              (op B.unop.left)) (Over.w h.unop)).symm).trans
          (NatTrans.naturality_apply
            ((sheafificationAdjunction J (Type u)).unit.app (yoneda.obj U))
            (h.unop.left).op A.unop.hom) }

/-- **The tautological section is constant.** It does not depend on the sheaf it is taken on:
precomposing it with any map of sheaves on `C/U` gives the tautological section again. -/
theorem comp_tautologicalSection {W W' : Sheaf (J.over U) (Type u)} (f : W ⟶ W') :
    f ≫ tautologicalSection U J W' = tautologicalSection U J W :=
  rfl

/-- The adjunct, under the Stacks 03CD adjunction followed by sheafification on `C`, of the
sheafification of `prodSnd` is the adjunct, under sheafification on `C/U`, of the tautological
section. -/
theorem presheafUnitLevel (F : Cᵒᵖ ⥤ Type u) :
    ((presheafAdjunction (U := U)).comp (sheafificationAdjunction J (Type u))).unit.app
          (restrict.obj F) ≫
        (localizationPullback U J ⋙ sheafToPresheaf (J.over U) (Type u)).map
          ((presheafToSheaf J (Type u)).map (prodSnd U F)) =
      (sheafificationAdjunction (J.over U) (Type u)).unit.app (restrict.obj F) ≫
        (sheafToPresheaf (J.over U) (Type u)).map
          (tautologicalSection U J
            ((presheafToSheaf (J.over U) (Type u)).obj (restrict.obj F))) := by
  have htaut : (presheafAdjunction (U := U)).unit.app (restrict.obj F) ≫
        restrict.map (prodSnd U F ≫
          (sheafificationAdjunction J (Type u)).unit.app (yoneda.obj U)) =
      (sheafificationAdjunction (J.over U) (Type u)).unit.app (restrict.obj F) ≫
        (sheafToPresheaf (J.over U) (Type u)).map
          (tautologicalSection U J
            ((presheafToSheaf (J.over U) (Type u)).obj (restrict.obj F))) := by
    refine NatTrans.ext (funext fun A => ?_)
    ext s
    rfl
  have hnat : (presheafAdjunction (U := U)).unit.app (restrict.obj F) ≫
        restrict.map ((sheafificationAdjunction J (Type u)).unit.app
            (presheafFunctor.obj (restrict.obj F)) ≫
          (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)).map (prodSnd U F)) =
      (sheafificationAdjunction (J.over U) (Type u)).unit.app (restrict.obj F) ≫
        (sheafToPresheaf (J.over U) (Type u)).map
          (tautologicalSection U J
            ((presheafToSheaf (J.over U) (Type u)).obj (restrict.obj F))) :=
    (congrArg
      (fun m => (presheafAdjunction (U := U)).unit.app (restrict.obj F) ≫ restrict.map m)
      ((sheafificationAdjunction J (Type u)).unit.naturality (prodSnd U F)).symm).trans htaut
  exact (eq_whisker
        (Adjunction.comp_unit_app (presheafAdjunction (U := U))
          (sheafificationAdjunction J (Type u)) (restrict.obj F))
        ((localizationPullback U J ⋙ sheafToPresheaf (J.over U) (Type u)).map
          ((presheafToSheaf J (Type u)).map (prodSnd U F)))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
            (fun m => (presheafAdjunction (U := U)).unit.app (restrict.obj F) ≫ m)
            (restrict.map_comp
              ((sheafificationAdjunction J (Type u)).unit.app
                (presheafFunctor.obj (restrict.obj F)))
              ((presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)).map
                (prodSnd U F))).symm).trans
        hnat))

/-- **Stacks 03CD followed by the sheafification of `prodSnd` is the adjunct of the tautological
section.** The comparison `sheafifyNatIso` of the two left adjoints, followed by the map to
`h_U^#` that remembers only the index, is the adjunct under `j_{U!} ⊣ j_U^{-1}` of the
tautological section of `h_U^#`. -/
theorem sheafifyNatIso_hom_app_comp_prodSnd (F : Cᵒᵖ ⥤ Type u) :
    (sheafifyNatIso J).hom.app (restrict.obj F) ≫
        (presheafToSheaf J (Type u)).map (prodSnd U F) =
      (localizationShriek U J).map
          (tautologicalSection U J
            ((presheafToSheaf (J.over U) (Type u)).obj (restrict.obj F))) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).counit.app
          ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) :=
  Stacks.CategoryTheory.leftAdjointUniq_hom_app_comp_of_unit
    (sheafificationAdjunction (J.over U) (Type u))
    ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)
    ((presheafAdjunction (U := U)).comp (sheafificationAdjunction J (Type u)))
    (restrict.obj F) ((presheafToSheaf J (Type u)).obj (yoneda.obj U))
    ((presheafToSheaf J (Type u)).map (prodSnd U F))
    (tautologicalSection U J ((presheafToSheaf (J.over U) (Type u)).obj (restrict.obj F)))
    (presheafUnitLevel U J F)

/-- The `prod.fst` component of Stacks 03EE is the composite of the sheafification counit of
`C/U`, Stacks 03CD, and the sheafification of `prodSnd`. -/
theorem overShriekOverPullbackNatIso_hom_app_prod_fst_aux (X : Sheaf J (Type u)) :
    (overShriekOverPullbackNatIso U J).hom.app X ≫ prod.fst =
      (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
        (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
          (presheafToSheaf J (Type u)).map (prodSnd U ((sheafToPresheaf J (Type u)).obj X)) := by
  refine Eq.trans (congrArg (· ≫ prod.fst) (overShriekOverPullbackNatIso_hom_app U J X)) ?_
  show (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
      (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
        (presheafToSheaf J (Type u)).map
            (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
              (prodFst U ((sheafToPresheaf J (Type u)).obj X))) ≫
          prodComparison (presheafToSheaf J (Type u)) (yoneda.obj U)
              ((sheafToPresheaf J (Type u)).obj X) ≫
            prod.map (𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
                ((sheafificationAdjunction J (Type u)).counit.app X) ≫ prod.fst =
    (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
      (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
        (presheafToSheaf J (Type u)).map (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
  rw [prod.map_fst, Category.comp_id, prodComparison_fst, ← Functor.map_comp]
  exact congrArg
    (fun m => (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
      (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
        (presheafToSheaf J (Type u)).map m)
    (prod.lift_fst (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
      (prodFst U ((sheafToPresheaf J (Type u)).obj X)))

/-- **The `prod.fst` component of Stacks 03EE is the tautological section.** The isomorphism
`j_{U!}j_U^{-1}F ≅ h_U^# × F`, followed by the projection onto `h_U^#`, is the adjunct under
`j_{U!} ⊣ j_U^{-1}` of the tautological section of `h_U^#` over `C/U`. -/
theorem overShriekOverPullbackNatIso_hom_app_prod_fst (X : Sheaf J (Type u)) :
    (overShriekOverPullbackNatIso U J).hom.app X ≫ prod.fst =
      (localizationShriek U J).map (tautologicalSection U J ((localizationPullback U J).obj X)) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).counit.app
          ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) :=
  (overShriekOverPullbackNatIso_hom_app_prod_fst_aux U J X).trans
    ((congrArg
          (fun m => (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫ m)
          (sheafifyNatIso_hom_app_comp_prodSnd U J ((sheafToPresheaf J (Type u)).obj X))).trans
      ((Category.assoc _ _ _).symm.trans
        (eq_whisker
          (((localizationShriek U J).map_comp ((overPullbackNatIso U J).inv.app X)
                (tautologicalSection U J
                  ((presheafToSheaf (J.over U) (Type u)).obj
                    ((sheafToPresheaf J (Type u) ⋙ restrict).obj X)))).symm.trans
            (congrArg (localizationShriek U J).map
              (comp_tautologicalSection U J ((overPullbackNatIso U J).inv.app X))))
          (((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).counit.app
            ((presheafToSheaf J (Type u)).obj (yoneda.obj U))))))

end CategoryTheory.OverShriek

end
