module

public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanEvaluation
public import StacksFrontier.CategoryTheory.Sites.PushforwardSections

/-!
# The two-fibre product over a slice is the index category of the right Kan extension

Let `f : 𝒳 ⥤ 𝒴` be a functor over `𝒞` with `p𝒴 : 𝒴 ⥤ 𝒞` fibred in groupoids, and let `Y` be an
object of `𝒴` together with a 1-morphism `𝒞/p𝒴(Y) ⥤ 𝒴` sending the final object to `Y` through
strongly cartesian lifts (a `CategoryTheory.Functor.CartesianSliceDatum`, for instance the one of
a choice of pullbacks). The right Kan extension along `f.op` is computed at `Y` as a limit over
the category `CostructuredArrow f Y` of arrows `f(x) ⟶ Y`, and Stacks 06W6 identifies it with
the global sections over the two-fibre product `(𝒞/p𝒴(Y)) ×_𝒴 𝒳`, through the functor
`CategoryTheory.Presheaf.pushforwardIndexFunctor` from the two-fibre product to
`CostructuredArrow f Y`.

This file records that this functor is an **equivalence of categories**, so that the two-fibre
product and the comma category are interchangeable as index categories, and as sites; together
with the two-fibre product's projection to `𝒳` being faithful as soon as the slice is faithful
over the base.

## Main results

* `CategoryTheory.TwoFibreProductOver.Hom.ext_of_b`: a morphism of a two-fibre product whose
  first factor is faithful over the base is determined by its second component.
* `CategoryTheory.TwoFibreProductOver.faithful_snd`: the second projection is then faithful.
* `CategoryTheory.Presheaf.pushforwardIndexFunctor_isEquivalence`: the comparison functor of
  Stacks 06W6 is an equivalence.
* `CategoryTheory.Presheaf.ranEvaluationIsoLimTwoFibreProduct`: **Stacks 06W6 in limit form, for
  coefficients in any category**: the right Kan extension along `f.op` evaluated at `Y` is the
  limit over the two-fibre product of the restriction along its projection to `𝒳`, naturally in
  the functor extended.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳] {𝒴 : Type*} [Category* 𝒴]
  {𝒮 : Type*} [Category* 𝒮] {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮}
  {G : 𝒴 ⥤ 𝒮}

/-- The base morphism of a morphism of the 2-fibre product is determined by its
`𝒴`-component, since that component lies over it. -/
lemma Hom.hbase_eq_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : P ⟶ Q) :
    f.hbase = eqToHom P.hy.symm ≫ p𝒴.map f.b ≫ eqToHom Q.hy := by
  have := f.hb
  rw [IsHomLift.fac' p𝒴 f.hbase f.b]
  simp

/-- When the structure functor of the first factor is faithful, a morphism of the 2-fibre
product is determined by its second component: the second component determines the base
morphism, and the first component lies over it. -/
lemma Hom.ext_of_b [p𝒳.Faithful] {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {f g : P ⟶ Q}
    (hb : f.b = g.b) : f = g := by
  have hbase : f.hbase = g.hbase := by rw [f.hbase_eq_b, g.hbase_eq_b, hb]
  refine Hom.ext' (p𝒳.map_injective ?_) hb
  have e1 := f.hbase_eq
  have e2 := g.hbase_eq
  rw [hbase, e2] at e1
  have := congrArg (fun k => eqToHom P.hx ≫ k ≫ eqToHom Q.hx.symm) e1
  simpa using this.symm

/-- The second projection of a 2-fibre product whose first factor is faithful over the base is
faithful. -/
instance faithful_snd [p𝒳.Faithful] : (snd p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective h := Hom.ext_of_b h

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.Presheaf

variable {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳] {𝒴 : Type*} [Category* 𝒴]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) {Y : 𝒴} (D : p𝒴.CartesianSliceDatum Y)

/-- The comparison functor of Stacks 06W6 is faithful: a morphism of the two-fibre product is
determined by its component in `𝒳`, the slice being faithful over the base. -/
instance pushforwardIndexFunctor_faithful : (pushforwardIndexFunctor p𝒳 p𝒴 f D).Faithful where
  map_injective {_ _} _ _ h :=
    TwoFibreProductOver.Hom.ext_of_b (congrArg CommaMorphism.left h)

variable (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)

include hf in
/-- The comparison functor of Stacks 06W6 is full: a morphism `f(x) ⟶ f(x')` over `Y` of the
`𝒳`-components of two objects of the two-fibre product is completed by the slice morphism it
lies over, the comparison square commuting because the chosen lifts are strongly cartesian. -/
lemma pushforwardIndexFunctor_full : (pushforwardIndexFunctor p𝒳 p𝒴 f D).Full where
  map_surjective {P Q} h := by
    have hP := pushforwardIndexUnit_left p𝒳 p𝒴 f D hf P
    have hQ := pushforwardIndexUnit_left p𝒳 p𝒴 f D hf Q
    have hαP := pushforwardIndexUnit_hα p𝒳 p𝒴 f D hf P
    have hαQ := pushforwardIndexUnit_hα p𝒳 p𝒴 f D hf Q
    let b : P.y ⟶ Q.y := h.left
    have hw : f.map b ≫ Q.iso.inv ≫ D.cone Q.x = P.iso.inv ≫ D.cone P.x := by
      simpa using h.w
    let aL : P.x.left ⟶ Q.x.left := eqToHom hP.symm ≫ p𝒴.map (f.map b) ≫ eqToHom hQ
    have haL : aL ≫ Q.x.hom = P.x.hom := by
      have h1 : p𝒴.map (f.map b) ≫ p𝒴.map (Q.iso.inv ≫ D.cone Q.x) =
          p𝒴.map (P.iso.inv ≫ D.cone P.x) := by
        rw [← Functor.map_comp, hw]
      rw [← hαQ, ← hαP] at h1
      simp only [aL, Category.assoc]
      rw [h1]
      simp
    let a : P.x ⟶ Q.x := Over.homMk aL haL
    have hb : p𝒴.IsHomLift a.left (f.map b) :=
      IsHomLift.of_fac' p𝒴 _ _ hP hQ (by simp [a, aL])
    refine ⟨TwoFibreProductOver.Hom.mk' a b ?_
      (pushforwardIndexSliceMor_map_comp_iso_hom p𝒳 p𝒴 f D a b hb hw.symm), ?_⟩
    · have := Functor.congr_hom hf.symm b
      simp only [Functor.comp_map] at this
      simp [a, aL, this]
    · apply CostructuredArrow.hom_ext
      rfl

include h𝒴 hf in
/-- The comparison functor of Stacks 06W6 is essentially surjective, indeed surjective on
objects: `CategoryTheory.Presheaf.pushforwardIndexInverse` is a section of it. -/
lemma pushforwardIndexFunctor_essSurj : (pushforwardIndexFunctor p𝒳 p𝒴 f D).EssSurj where
  mem_essImage Z := ⟨(pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).obj Z,
    ⟨eqToIso (pushforwardIndexFunctor_inverse_obj_eq p𝒳 p𝒴 f D h𝒴 hf Z)⟩⟩

include h𝒴 hf in
/-- **The two-fibre product `(𝒞/p𝒴(Y)) ×_𝒴 𝒳` is equivalent to the comma category of arrows
`f(x) ⟶ Y`**, through the comparison functor of Stacks 06W6, which sends a pair to its
comparison arrow to `Y`. -/
lemma pushforwardIndexFunctor_isEquivalence :
    (pushforwardIndexFunctor p𝒳 p𝒴 f D).IsEquivalence :=
  have := pushforwardIndexFunctor_full p𝒳 p𝒴 f D hf
  have := pushforwardIndexFunctor_essSurj p𝒳 p𝒴 f D h𝒴 hf
  { }

/-- **Stacks 06W6 in limit form.** The right Kan extension along `f.op` of a functor
`𝒳ᵒᵖ ⥤ H`, evaluated at `Y`, is the limit over the two-fibre product `(𝒞/p𝒴(Y)) ×_𝒴 𝒳` of its
restriction along the projection to `𝒳`, naturally in the functor extended.

The right Kan extension at `Y` is a limit over `StructuredArrow (op Y) f.op`
(`CategoryTheory.Functor.ranObjNatIsoLimit`), and the comparison functor of Stacks 06W6 is an
equivalence (`pushforwardIndexFunctor_isEquivalence`), hence initial; restricted along it, the
projection of the comma category becomes the projection of the two-fibre product on the nose. -/
noncomputable def ranEvaluationIsoLimTwoFibreProduct (H : Type*) [Category* H]
    [∀ G : 𝒳ᵒᵖ ⥤ H, f.op.HasPointwiseRightKanExtension G]
    [HasLimitsOfShape (TwoFibreProductOver (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f)ᵒᵖ H] :
    f.op.ran ⋙ (evaluation 𝒴ᵒᵖ H).obj (op Y) ≅
      (Functor.whiskeringLeft _ _ H).obj
          (TwoFibreProductOver.snd (Over.forget (p𝒴.obj Y)) p𝒳 p𝒴 D.sliceMor f).op ⋙ lim := by
  let E := (pushforwardIndexFunctor p𝒳 p𝒴 f D).op ⋙
    (costructuredArrowOpEquivalence f Y).functor
  have := pushforwardIndexFunctor_isEquivalence p𝒳 p𝒴 f D h𝒴 hf
  have : E.IsEquivalence := inferInstance
  have : HasLimitsOfShape (StructuredArrow (op Y) f.op) H :=
    hasLimitsOfShape_of_equivalence E.asEquivalence
  exact Functor.ranObjNatIsoLimit H f.op (op Y) ≪≫
    Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ H).obj (StructuredArrow.proj (op Y) f.op))
      (Functor.Initial.limIso E).symm

end CategoryTheory.Presheaf

end
