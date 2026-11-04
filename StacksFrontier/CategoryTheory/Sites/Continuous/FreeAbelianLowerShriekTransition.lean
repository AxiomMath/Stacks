module

public import StacksFrontier.CategoryTheory.Sites.Continuous.FreeAbelianLowerShriekComp
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.ShriekRestrictionTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekFreeAbelianNaturality

/-!
# The relocalization triangle of extensions by zero, as a composition comparison

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`. The
transformation `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` of
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` is built, through
`Stacks.CategoryTheory.shriekTransition`, from the comparison
`Stacks.CategoryTheory.restrictionLeftAdjointIso` of the left adjoints of the relocalization
triangle, which is an isomorphism `j_{M!} ≅ r_{f!} j_{N!}`.

That same isomorphism is `CategoryTheory.Functor.lowerShriekComp` — extension by zero along a
composite is the composite of the extensions by zero — read at the three continuous site functors
`r_f : C/M ⥤ C/N`, `j_N : C/N ⥤ C` and `j_M : C/M ⥤ C` and the equality `r_f ⋙ j_N = j_M`. This
module identifies the two, which is what makes
`CategoryTheory.Functor.freeLowerShriekIso_comp` — the compatibility of the free abelian sheaf
functor with `lowerShriekComp`, that is the naturality in the semi-representable object of
`CategoryTheory.SemiRepresentable.freeSheafPullbackIso` — applicable to the shriek restriction
transition.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_left`: in a comparison of two left
  adjoints of isomorphic right adjoints it does not matter which of the two adjunctions is read
  through the isomorphism.
* `CategoryTheory.SemiRepresentable.restrictionLeftAdjointIso_eq_lowerShriekComp`: **the
  identification.**
* `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality'`: the `hom` form of
  `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality`, which is stated on the
  inverses of the three commutations.

## Implementation notes

Both isomorphisms are a `CategoryTheory.Adjunction.leftAdjointUniq` of the localization adjunction
of `j_M` against the composite of the adjunctions of `r_f` and `j_N`, read through the comparison
`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso'` of the right adjoints, and
they differ only in which of the two adjunctions carries that comparison. The general lemma
exchanging the two sides is proved from the unit characterization
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` of `leftAdjointUniq` together with the
naturality of the comparison; the repository already has the mate-level statements
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight` and
`CategoryTheory.Mates.leftAdjointUniq_ofNatIsoRight_eq`, but both put the transport on the second
adjunction, which is the side that `lowerShriekComp` uses and `restrictionLeftAdjointIso` does
not.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]

/-- **Transporting the right adjoint along an isomorphism may be done on either side of a
comparison of left adjoints.** -/
theorem leftAdjointUniq_ofNatIsoRight_left {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R₁) :
    leftAdjointUniq (adj₁.ofNatIsoRight e.symm) adj₂ =
      leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e) := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  refine (adj₁.homEquiv x _).injective ?_
  rw [homEquiv_unit, homEquiv_unit,
    unit_leftAdjointUniq_hom_app adj₁ (adj₂.ofNatIsoRight e) x, ofNatIsoRight_unit]
  have hnat := e.hom.naturality
    ((leftAdjointUniq (adj₁.ofNatIsoRight e.symm) adj₂).hom.app x)
  have hu := unit_leftAdjointUniq_hom_app (adj₁.ofNatIsoRight e.symm) adj₂ x
  rw [ofNatIsoRight_unit] at hu
  refine Eq.trans ?_ (congrArg (fun m => m ≫ e.hom.app (L₂.obj x)) hu)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc, hnat]
  rw [← Category.assoc (e.inv.app (L₁.obj x)), e.inv_hom_id_app, Category.id_comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
  (Jm : GrothendieckTopology (ComponentOver M)) (Jn : GrothendieckTopology (ComponentOver N))
  (A : Type t) [Category.{u} A]
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget N).IsContinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn]
  [HasWeakSheafify Jm A] [HasWeakSheafify Jn A] [HasWeakSheafify J A]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ A, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverMap f).op.HasLeftKanExtension F]

omit [HasWeakSheafify Jm A] in
/-- **The comparison of left adjoints of the relocalization triangle is the composition
comparison of extensions by zero.** The isomorphism `j_{M!} ≅ r_{f!} j_{N!}` that
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` is built from is
`CategoryTheory.Functor.lowerShriekComp` for the three site functors `r_f`, `j_N`, `j_M` and the
equality `r_f ⋙ j_N = j_M`.

Both are a `CategoryTheory.Adjunction.leftAdjointUniq` of the localization adjunction of `j_M`
against the composite of the adjunctions of `r_f` and `j_N`, read through the comparison
`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso'` of the right adjoints; they
differ only in which of the two adjunctions carries that comparison, which is
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_left`. -/
theorem restrictionLeftAdjointIso_eq_lowerShriekComp :
    Stacks.CategoryTheory.restrictionLeftAdjointIso
        (relocalizationForgetPushforwardIso' J f Jm Jn A)
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N)
          A Jn J)
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M)
          A Jm J)
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
          A Jm Jn) =
      Functor.lowerShriekComp Jm Jn J (componentOverMap f) (componentOverForget N)
        (componentOverForget M) A
        (eqToIso (componentOverMap_comp_componentOverForget f)) :=
  Adjunction.leftAdjointUniq_ofNatIsoRight_left
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M) A Jm J)
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
        A Jm Jn).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N)
        A Jn J))
    (relocalizationForgetPushforwardIso' J f Jm Jn A)

end CategoryTheory.SemiRepresentable

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective (Type u)] {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

/-- **`freeSheafPushforwardIso` is natural in the semi-representable object, on the `hom` of the
three commutations.** This is
`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality`, which is stated on the
inverses, with all four isomorphisms of the square inverted.

That inversion cannot be carried out by `rw` -- the two spellings of the presheaf
`r_f.op ⋙ j_N.op ⋙ X ⋙ ℤ` obstruct it -- so the square is rebuilt as an equation of composites of
`CategoryTheory.Iso` and the inversion is `congrArg CategoryTheory.Iso.inv`.

The commutation of the free abelian sheaf functor with restriction along `r_f` is written as
`CategoryTheory.Functor.freePushforwardIso`, not as the Mathlib comparison it is built from: that
comparison is indexed by presheaves, and the presheaf it is read at here is
`r_f^{op} ⋙ (j_N^{op} ⋙ X ⋙ ℤ)` while the surrounding composites produce
`(j_N^{op} ⋙ X) ⋙ ℤ` -- the same presheaf by two expressions, which turns every use of this
square into a defeq check on a term large enough to exhaust the heartbeat budget of the
declaration using it. -/
theorem freeSheafPushforwardIso_naturality' (X : Sheaf J (Type u)) :
    (freeSheafPushforwardIso J M).hom.app X ≫
        (Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).map
          ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) (Type u)).inv.app X) =
      ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) AddCommGrpCat.{u}).inv.app
          ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X) ≫
        ((componentOverMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
              (componentwiseTopology J M) (componentwiseTopology J N)).map
            ((freeSheafPushforwardIso J N).hom.app X)) ≫
          (Functor.freePushforwardIso (componentwiseTopology J M)
              (componentwiseTopology J N) (componentOverMap f)).hom.app
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X) :=
  congrArg Iso.inv (Iso.ext (α := (Sheaf.composeAndSheafify (componentwiseTopology J M)
        AddCommGrpCat.free).mapIso
      ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
        (componentwiseTopology J N) (Type u)).app X) ≪≫
    ((freeSheafPushforwardIso J M).app X).symm)
    (β := (Functor.freePushforwardIso (componentwiseTopology J M)
          (componentwiseTopology J N) (componentOverMap f)).symm.app
        (((componentOverForget N).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J N) J).obj X) ≪≫
      ((componentOverMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (componentwiseTopology J M) (componentwiseTopology J N)).mapIso
          ((freeSheafPushforwardIso J N).app X).symm ≪≫
        (relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) AddCommGrpCat.{u}).app
          ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X))
    (freeSheafPushforwardIso_naturality J f X))

end CategoryTheory.SemiRepresentable

end
