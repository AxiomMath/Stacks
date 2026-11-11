module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassRestrictionToAnObject

/-!
# A first cohomology class over an object as an obstruction to lifting a section

Let `F` be an abelian sheaf on a site `(C, J)` whose category of abelian sheaves has enough
injectives, let `U` be an object of `C` and let `c ∈ H¹(U, F)`. Embed `F` into an injective
sheaf `I` with quotient `Q`. Then `c` is the boundary of a section `σ` of `Q` over `U`, and the
restriction of `c` along a morphism `g : V ⟶ U` vanishes as soon as the restriction of `σ` to
`V` lifts to a section of `I` over `V`.

The sections `i` of `I` over objects `g : V ⟶ U` of the slice with `π i = g^* σ` form a torsor
under `F` on the slice site over `U`; this file only records the short exact sequence, the
section `σ` and the vanishing criterion, which is what a geometric argument needs in order to
build that torsor and to kill `c` locally.

## Main results

* `Stacks.Cohomology.Torsors.freeYonedaSheafHomEquiv_precomp`: the corepresentation of
  evaluation by the free abelian sheaf on `yoneda.obj X` is natural in `X`.
* `Stacks.Cohomology.Torsors.exists_shortExact_cohomologyPresheaf_map_eq_zero_of_lift`: the
  short exact sequence, the section `σ` and the vanishing criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- **The corepresentation of evaluation is natural in the object**: precomposing with the map
of free abelian sheaves induced by `g : V ⟶ U` restricts the corresponding section along `g`. -/
public lemma freeYonedaSheafHomEquiv_precomp {V U : C} (g : V ⟶ U)
    (Q : Sheaf J AddCommGrpCat.{v}) (q : OverObjectCohomology.freeYonedaSheaf J U ⟶ Q) :
    OverObjectCohomology.freeYonedaSheafHomEquiv J V Q
        ((presheafToSheaf J AddCommGrpCat.{v}).map
          (Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free) ≫ q) =
      Q.obj.map g.op (OverObjectCohomology.freeYonedaSheafHomEquiv J U Q q) := by
  dsimp only [OverObjectCohomology.freeYonedaSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  rw [show Functor.whiskerRight (yoneda.map g) AddCommGrpCat.free =
    ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).map
      (yoneda.map g) from rfl]
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality' (F := Q.obj ⋙ forget AddCommGrpCat) _ g.op).symm

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **A first cohomology class over an object obstructs lifting a section of a quotient.** Let
`c ∈ H¹(U, F)`. There are a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of abelian sheaves and a
section `σ` of `Q` over `U` such that for every `g : V ⟶ U` along which the restriction of `σ`
lifts to a section of `I`, the restriction of `c` along `g` vanishes. -/
public theorem exists_shortExact_cohomologyPresheaf_map_eq_zero_of_lift
    (F : Sheaf J AddCommGrpCat.{v}) (U : C) (c : Sheaf.H' F 1 U) :
    ∃ (I Q : Sheaf J AddCommGrpCat.{v}) (ι : F ⟶ I) (π : I ⟶ Q) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact ∧ ∃ σ : Q.obj.obj (op U),
      ∀ ⦃V : C⦄ (g : V ⟶ U) (i : I.obj.obj (op V)),
        π.hom.app (op V) i = Q.obj.map g.op σ → (F.cohomologyPresheaf 1).map g.op c = 0 := by
  let ι : F ⟶ Injective.under F := Injective.ι F
  let Sc := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hSc : Sc.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  have : Injective Sc.X₂ := inferInstanceAs (Injective (Injective.under F))
  obtain ⟨q, hq⟩ := ext_one_boundary_surjective Sc hSc
    (OverObjectCohomology.freeYonedaSheaf J U) c
  refine ⟨_, _, ι, cokernel.π ι, cokernel.condition ι, hSc,
    OverObjectCohomology.freeYonedaSheafHomEquiv J U _ q, ?_⟩
  intro V g i hi
  rw [cohomologyPresheaf_map_apply, ← hq, Ext.mk₀_comp_mk₀_assoc]
  refine (ext_one_boundary_eq_zero_iff_lift Sc hSc _ _).2
    ⟨(OverObjectCohomology.freeYonedaSheafHomEquiv J V _).symm i, ?_⟩
  apply (OverObjectCohomology.freeYonedaSheafHomEquiv J V _).injective
  rw [OverObjectCohomology.freeYonedaSheafHomEquiv_comp, Equiv.apply_symm_apply,
    freeYonedaSheafHomEquiv_precomp]
  exact hi

end Stacks.Cohomology.Torsors

end
