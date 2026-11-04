module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives

/-!
# Finite local constancy of an abelian sheaf is a property of its underlying sheaf of sets

Let `(C, J)` be a site. An abelian sheaf `F` on `C` is finite locally constant exactly when the
sheaf of sets underlying it is: the condition sees only the underlying sets.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_forget` — the easy direction: composing a
  trivializing isomorphism with the comparison of constant sheaves under a forgetful functor
  turns a finite locally constant abelian sheaf into a finite locally constant sheaf of sets.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget` — the substantial direction: an
  abelian sheaf whose underlying sheaf of sets is finite locally constant is itself finite
  locally constant.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_forget` — the two together.

## Implementation notes

The hard direction is not formal. A trivializing covering for the underlying sheaf of sets gives,
on each member, a locally bijective map from a *constant* presheaf on a finite set `A` to the
underlying presheaf of sets of `F`; it carries no group structure, so the image of `A` need not
be a subgroup. The repair is to refine the covering once more. Over the terminal object of a
localized site one has finitely many sections — the sums, the negatives and the zero computed
from the image of `A` — and `Stacks.Sheafification.exists_cover_representatives` produces a
further covering on each member of which all of them are again in the image of `A`. On such a
member the image of `A` is closed under the group operations, so it is the carrier of a finite
subgroup `H` of the sections, and the map from the constant abelian sheaf on `H` to `F` is
locally bijective, hence an isomorphism by
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`.

The step just described is `Stacks.ConstantSheaf.isConstant_of_finite_range`, which is stated
separately because it is useful on its own. The refinement is assembled with
`Stacks.ConstantSheaf.exists_cover_trans`, transitivity of being covered by objects with a given
property, which the library already proves for sheaves of sets.

Throughout, a value of an abelian sheaf is pinned at the single spelling
`F.obj.obj (Opposite.op U)`, an object of `AddCommGrpCat`, rather than at the equal but
syntactically different `(F.obj ⋙ forget AddCommGrpCat).obj (Opposite.op U)`: the two agree only
at default transparency, so instance synthesis for `+` and `-` fails on the second spelling, and
quantifying at the first and letting the membership statements bridge by definitional equality
avoids the problem without any transparency option.

## Why no `@[stacks 0DV5]` attribute appears in this file

Tag 0DV5 identifies, for a connected scheme with a geometric point, the finite locally constant
sheaves on its small étale site with the finite continuous representations of its étale
fundamental group — in the sets-valued, abelian-group-valued and module-valued cases. The results
below are the sheaf-theoretic input which makes the abelian case a formal consequence of the
sets case: they say that the finite local constancy condition on an abelian sheaf is a condition
on the underlying sheaf of sets, so that the abelian sheaves in question are exactly the
commutative group objects among the finite locally constant sheaves of sets.

The tag itself is proved in the modules under
`StacksDraft.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant`: part (1) is
`AlgebraicGeometry.finiteLocallyConstantSetsEquivalence`, part (2) is
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence` and part (3) is
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`. What this file contributes
to them is the equivalence of conditions recorded below, which is site-independent and therefore
stated here rather than there.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ConstantSheaf

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A locally bijective comparison with a constant presheaf on a finite set whose image is
closed under the group operations makes an abelian sheaf constant.** Let `η` be a locally
bijective map from the constant presheaf on a finite set `A` to the presheaf of sets underlying
an abelian sheaf `R`. If the image of `A` in the sections of `R` over a terminal object `T`
contains zero and is closed under addition and negation, then that image is a finite subgroup
`H` of those sections, and `R` is the constant sheaf on `H`. -/
theorem isConstant_of_finite_range [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J AddCommGrpCat.{max u v}) (A : Type (max u v)) [Finite A]
    (η : (Functor.const Cᵒᵖ).obj A ⟶ R.obj ⋙ forget AddCommGrpCat)
    (hinj : Presheaf.IsLocallyInjective J η) (hsurj : Presheaf.IsLocallySurjective J η)
    {T : C} (hT : IsTerminal T)
    (hz : (0 : ToType (R.obj.obj (op T))) ∈ Set.range (η.app (op T)))
    (ha : ∀ x y : ToType (R.obj.obj (op T)), x ∈ Set.range (η.app (op T)) →
      y ∈ Set.range (η.app (op T)) → x + y ∈ Set.range (η.app (op T)))
    (hn : ∀ x : ToType (R.obj.obj (op T)), x ∈ Set.range (η.app (op T)) →
      -x ∈ Set.range (η.app (op T))) :
    ∃ H : AddCommGrpCat.{max u v}, Finite (ToType H) ∧
      Nonempty ((constantSheaf J AddCommGrpCat).obj H ≅ R) := by
  classical
  have := hinj
  have := hsurj
  let H : AddSubgroup (ToType (R.obj.obj (op T))) :=
    { carrier := Set.range (η.app (op T))
      zero_mem' := hz
      add_mem' := ha _ _
      neg_mem' := hn _ }
  let q : A → H := fun a ↦ ⟨η.app (op T) a, ⟨a, rfl⟩⟩
  have hq : Function.Surjective q := fun ⟨_, a, rfl⟩ ↦ ⟨a, rfl⟩
  have : Finite H := Finite.of_surjective q hq
  let ψ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of H) ⟶ R.obj :=
    { app V := AddCommGrpCat.ofHom ((R.obj.map (hT.from V.unop).op).hom.comp H.subtype)
      naturality V W f := by
        ext x
        show R.obj.map (hT.from W.unop).op x.val =
          R.obj.map f (R.obj.map (hT.from V.unop).op x.val)
        rw [← Functor.map_comp_apply,
          show (hT.from W.unop).op = (hT.from V.unop).op ≫ f from
            congrArg Quiver.Hom.op (hT.hom_ext _ _)] }
  let q' := (Functor.const Cᵒᵖ).map (TypeCat.ofHom q)
  let ψ' := Functor.whiskerRight ψ (forget AddCommGrpCat)
  have hfac : q' ≫ ψ' = η := by
    ext V a
    exact (NatTrans.naturality_apply η (hT.from V.unop).op a).symm
  have : Presheaf.IsLocallySurjective J q' :=
    Presheaf.isLocallySurjective_of_surjective J q' (fun _ ↦ hq)
  have : Presheaf.IsLocallyInjective J (q' ≫ ψ') := hfac.symm ▸ inferInstance
  have : Presheaf.IsLocallySurjective J (q' ≫ ψ') := hfac.symm ▸ inferInstance
  have : Presheaf.IsLocallyInjective J ψ' :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J q' ψ'
  have : Presheaf.IsLocallySurjective J ψ' :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J q' ψ'
  have : Presheaf.IsLocallyInjective J ψ :=
    (Presheaf.isLocallyInjective_forget_iff J ψ).mp inferInstance
  have : Presheaf.IsLocallySurjective J ψ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J ψ).mpr inferInstance
  let φ : (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of H) ⟶ R :=
    ⟨CategoryTheory.sheafifyLift J ψ R.property⟩
  have hφ : CategoryTheory.toSheafify J _ ≫ φ.hom = ψ :=
    CategoryTheory.toSheafify_sheafifyLift J ψ R.property
  have : Sheaf.IsLocallyInjective φ :=
    (Presheaf.comp_isLocallyInjective_iff J (CategoryTheory.toSheafify J _) φ.hom).mp
      (hφ ▸ inferInstance)
  have : Sheaf.IsLocallySurjective φ :=
    (Presheaf.comp_isLocallySurjective_iff J (CategoryTheory.toSheafify J _) φ.hom).mp
      (hφ ▸ inferInstance)
  have := (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨inferInstance, inferInstance⟩
  exact ⟨AddCommGrpCat.of H, inferInstance, ⟨asIso φ⟩⟩

/-- **The underlying sheaf of sets of a finite locally constant abelian sheaf is finite locally
constant.** A trivializing covering for the abelian sheaf is one for the underlying sheaf of
sets, because the forgetful functor to sets takes a constant abelian sheaf to the constant sheaf
on the underlying set. -/
theorem isFiniteLocallyConstant_forget
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (F : Sheaf J AddCommGrpCat.{max u v}) (hF : IsFiniteLocallyConstant J F) :
    IsFiniteLocallyConstant J ((sheafCompose J (forget AddCommGrpCat.{max u v})).obj F) where
  exists_finite_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
    refine ⟨I, X, f, hf, fun i ↦ ?_⟩
    obtain ⟨A, hA, ⟨e⟩⟩ := h i
    exact ⟨(forget AddCommGrpCat.{max u v}).obj A, hA,
      ⟨((constantCommuteCompose (J.over (X i)) (forget AddCommGrpCat.{max u v})).app A).symm ≪≫
        (sheafCompose (J.over (X i)) (forget AddCommGrpCat.{max u v})).mapIso e⟩⟩

/-- **An abelian sheaf whose underlying sheaf of sets is finite locally constant is itself finite
locally constant.**

The trivializing covering of the underlying sheaf of sets gives, over each member `X i`, a
locally bijective map from a constant presheaf on a finite set `A`; its image need not be a
subgroup, so the covering is refined once more so that the finitely many sections obtained from
the image of `A` by the group operations are again in that image, and
`Stacks.ConstantSheaf.isConstant_of_finite_range` applies on each member of the refinement. -/
theorem isFiniteLocallyConstant_of_forget
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (F : Sheaf J AddCommGrpCat.{max u v})
    (hF : IsFiniteLocallyConstant J
      ((sheafCompose J (forget AddCommGrpCat.{max u v})).obj F)) :
    IsFiniteLocallyConstant J F := by
  classical
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, X, f, hf, hloc⟩ := hF.exists_finite_cover U
  refine exists_cover_trans J (P := fun V ↦ ∃ E : AddCommGrpCat.{max u v},
    Finite (ToType E) ∧ Nonempty ((constantSheaf (J.over V) AddCommGrpCat).obj E ≅
      (J.overPullback AddCommGrpCat V).obj F)) hf fun i ↦ ?_
  obtain ⟨A, hA, ⟨e⟩⟩ := hloc i
  have : Finite A := hA
  have : Fintype A := Fintype.ofFinite A
  have hIso : IsIso e.hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (J.over (X i)) (Type (max u v))).map e.hom))
  have heS : Presheaf.IsLocallySurjective (J.over (X i)) e.hom.hom := inferInstance
  have heI : Presheaf.IsLocallyInjective (J.over (X i)) e.hom.hom := inferInstance
  have htS : Presheaf.IsLocallySurjective (J.over (X i))
      (CategoryTheory.toSheafify (J.over (X i))
        ((Functor.const (Over (X i))ᵒᵖ).obj A)) := inferInstance
  have htI : Presheaf.IsLocallyInjective (J.over (X i))
      (CategoryTheory.toSheafify (J.over (X i))
        ((Functor.const (Over (X i))ᵒᵖ).obj A)) := inferInstance
  -- The comparison map from the constant presheaf on `A`, used only through its local
  -- bijectivity, so its construction is discarded at once.
  obtain ⟨η, hSurj, hInj⟩ : ∃ η : (Functor.const (Over (X i))ᵒᵖ).obj A ⟶
      ((J.overPullback AddCommGrpCat.{max u v} (X i)).obj F).obj ⋙ forget AddCommGrpCat,
      Presheaf.IsLocallySurjective (J.over (X i)) η ∧
        Presheaf.IsLocallyInjective (J.over (X i)) η :=
    -- The two instance arguments are supplied positionally: the middle presheaf of the
    -- composite has two spellings, `sheafify J' (const A)` and `((constantSheaf J').obj A).obj`,
    -- which agree only at default transparency, so instance synthesis cannot bridge them.
    ⟨CategoryTheory.toSheafify (J.over (X i)) _ ≫ e.hom.hom,
      @Presheaf.isLocallySurjective_comp _ _ (J.over (X i)) _ _ _ _ _ _ _ _ _
        (CategoryTheory.toSheafify (J.over (X i)) _) e.hom.hom htS heS,
      @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ (J.over (X i)) _ _ _
        (CategoryTheory.toSheafify (J.over (X i)) _) e.hom.hom htI heI⟩
  -- The finitely many sections over the terminal object of the localized site which the group
  -- operations produce from the image of `A`: the sums, the negatives and zero.
  obtain ⟨L, W, p, hp, hrep⟩ := Stacks.Sheafification.exists_cover_representatives
    (D := Type (max u v)) (J.over (X i)) η (Over.mk (𝟙 (X i)))
    (fun j ↦ (Fintype.equivFin ((A × A) ⊕ (A ⊕ PUnit.{1}))).symm j |>.elim
      (fun ab ↦ η.app (op (Over.mk (𝟙 (X i)))) ab.1 + η.app (op (Over.mk (𝟙 (X i)))) ab.2)
      (Sum.elim (fun a ↦ -η.app (op (Over.mk (𝟙 (X i)))) a) (fun _ ↦ 0)))
  refine ⟨L, fun l ↦ (W l).left, fun l ↦ (p l).left, ?_, fun l ↦ ?_⟩
  · rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hp
  · -- Every section of the displayed finite list is in the image of `A` already over `W l`.
    have hr (z : (A × A) ⊕ (A ⊕ PUnit.{1})) :
        ∃ a : A, ((J.overPullback AddCommGrpCat.{max u v} (X i)).obj F).obj.map (p l).op
          (z.elim (fun ab ↦ η.app (op (Over.mk (𝟙 (X i)))) ab.1 +
              η.app (op (Over.mk (𝟙 (X i)))) ab.2)
            (Sum.elim (fun a ↦ -η.app (op (Over.mk (𝟙 (X i)))) a) (fun _ ↦ 0))) =
          η.app (op (W l)) a := by
      obtain ⟨a, ha⟩ := (hrep l).2 (Fintype.equivFin ((A × A) ⊕ (A ⊕ PUnit.{1})) z)
      exact ⟨a, by rwa [Equiv.symm_apply_apply] at ha⟩
    have hc (a : A) : ((J.overPullback AddCommGrpCat.{max u v} (X i)).obj F).obj.map (p l).op
        (η.app (op (Over.mk (𝟙 (X i)))) a) = η.app (op (W l)) a :=
      (NatTrans.naturality_apply η (p l).op a).symm
    -- Over the terminal object of the site localized at `W l`, the comparison map is the one
    -- over `W l` itself: the connecting morphism is the identity on underlying objects.
    have he : (Functor.whiskerLeft (Over.map (W l).hom).op η).app
        (op (Over.mk (𝟙 (W l).left))) = η.app (op (W l)) := by
      refine ConcreteCategory.ext_apply fun a ↦ ?_
      refine (NatTrans.naturality_apply η (Over.homMk (𝟙 (W l).left) (by simp) :
        (Over.map (W l).hom).obj (Over.mk (𝟙 (W l).left)) ⟶ W l).op a).trans ?_
      simp only [Functor.comp_obj, Functor.comp_map,
        Functor.sheafPushforwardContinuous_obj_obj_map, Over.forget_obj, Over.map_obj_left,
        Over.mk_left, Quiver.Hom.unop_op, Over.forget_map, Over.homMk_left, op_id,
        CategoryTheory.Functor.map_id, TypeCat.ofHom_apply, Functor.const_obj_obj,
        Functor.op_obj]
      exact ConcreteCategory.id_apply _
    -- The three closure properties, proved over `W l` where every term is type-correct at
    -- `implicit` transparency, and transported to the terminal object of the localized site by
    -- a single rewrite along `he` followed by a term-mode `exact`.
    have hz : (0 : ToType (((J.overPullback AddCommGrpCat.{max u v} (X i)).obj F).obj.obj
        (op (W l)))) ∈ Set.range (η.app (op (W l))) := by
      obtain ⟨a, ha⟩ := hr (.inr (.inr PUnit.unit))
      exact ⟨a, by rw [← ha, Sum.elim_inr, Sum.elim_inr, map_zero]⟩
    have hadd : ∀ a b : A,
        η.app (op (W l)) a + η.app (op (W l)) b ∈ Set.range (η.app (op (W l))) := fun a b ↦ by
      obtain ⟨c, h⟩ := hr (.inl (a, b))
      exact ⟨c, by rw [← h, Sum.elim_inl, map_add, hc, hc]; rfl⟩
    have hneg : ∀ a : A, -η.app (op (W l)) a ∈ Set.range (η.app (op (W l))) := fun a ↦ by
      obtain ⟨b, h⟩ := hr (.inr (.inl a))
      exact ⟨b, by rw [← h, Sum.elim_inr, Sum.elim_inl, ← hc a]; exact map_neg _ _⟩
    refine isConstant_of_finite_range (J.over (W l).left)
      ((J.overPullback AddCommGrpCat.{max u v} (W l).left).obj F) A
      (Functor.whiskerLeft (Over.map (W l).hom).op η)
      (Presheaf.isLocallyInjective_whisker (J.over (W l).left) (J.over (X i))
        (Over.map (W l).hom) η)
      (Presheaf.isLocallySurjective_whisker (J.over (W l).left) (J.over (X i))
        (Over.map (W l).hom) η) Over.mkIdTerminal ?_ ?_ ?_
    · rw [he]; exact hz
    · rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
      rw [he]; exact hadd a b
    · rintro x ⟨a, rfl⟩
      rw [he]; exact hneg a

/-- **An abelian sheaf is finite locally constant exactly when its underlying sheaf of sets
is.** -/
theorem isFiniteLocallyConstant_iff_forget
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsFiniteLocallyConstant J F ↔
      IsFiniteLocallyConstant J ((sheafCompose J (forget AddCommGrpCat.{max u v})).obj F) :=
  ⟨isFiniteLocallyConstant_forget J F, isFiniteLocallyConstant_of_forget J F⟩

end Stacks.ConstantSheaf

end
