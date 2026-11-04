module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Continuity

/-!
# Sheaves on the site of a semi-representable object

Let `(C, J)` be a site and `K = ⨿ i, K.obj i` a semi-representable object of `C`. This file
proves the three decompositions that make the site `C / K` of Stacks 85.15 usable.

First, a sheaf on `C / K` is the same thing as a family of sheaves on the slice sites
`C / K.obj i`: the equivalence restricts the underlying presheaf along each component inclusion,
and its inverse assembles a family into a single presheaf on the disjoint union. This holds for
sheaves valued in any category.

Second, sheafifying the semi-representable presheaf `F(K)` attached to `K` gives the coproduct
of the sheafifications of the representables `K.obj i`, compatibly with the injections;
sheafification is a left adjoint, so it preserves the coproduct that defines `F(K)`.

Third, the slice category over that sheaf is the product of the slice categories over its
components, the equivalence being given componentwise by pullback along the injections. This
is where van Kampen descent enters: coproducts of types are van Kampen colimits, hence so are
coproducts of presheaves (evaluation detects them) and, by passing through the sheafification
reflection, coproducts of sheaves.

## Main definitions

* `CategoryTheory.SemiRepresentable.sigmaOpFunctor`: the comparison
  `(Σ i, D i)ᵒᵖ ⥤ Σ i, (D i)ᵒᵖ`.
* `CategoryTheory.SemiRepresentable.componentPresheaf`,
  `CategoryTheory.SemiRepresentable.assembleSheaf`: a family of sheaves on the components,
  assembled into one sheaf on `C / K`.
* `CategoryTheory.SemiRepresentable.restrictSheaf`: restriction of a sheaf on `C / K` to the
  components.
* `CategoryTheory.SemiRepresentable.assembleOver`,
  `CategoryTheory.SemiRepresentable.coproductFamilyIso`,
  `CategoryTheory.SemiRepresentable.overCoproductEquivalence`: the slice category over a van
  Kampen coproduct is the product of the slice categories over its summands.
* `CategoryTheory.SemiRepresentable.assembleOverCompPullbackIso` and
  `CategoryTheory.SemiRepresentable.isEquivalence_assembleOver`: the assembling functor is the
  quasi-inverse of that equivalence, so it is itself an equivalence.

## Main results

* `CategoryTheory.SemiRepresentable.formalCoproductSliceSheavesEquivalence`: sheaves on `C / K`
  are families of sheaves on the component slices, together with the canonical componentwise
  restriction isomorphisms.
* `CategoryTheory.SemiRepresentable.sheafificationFormalCoproductIso`: the coproduct
  decomposition of the sheaf associated to `K`, respecting the canonical injections.
* `CategoryTheory.SemiRepresentable.sheavesOverSheafificationFormalCoproductEquivalence`: the
  slice decomposition, with forward functor the componentwise pullbacks.
* `CategoryTheory.SemiRepresentable.isVanKampenColimit_types`,
  `CategoryTheory.SemiRepresentable.isVanKampenColimit_presheafCoproduct`,
  `CategoryTheory.SemiRepresentable.isVanKampenColimit_sheafCoproduct`: coproducts of types, of
  presheaves of types and of sheaves of types are van Kampen.

## Implementation notes

Mathlib's `CategoryTheory.FinitaryExtensive` gives van Kampen descent only for *finite*
coproducts, while a semi-representable object has an arbitrary index type; the three van Kampen
lemmas here are therefore proved from scratch, the one about types elementwise and the other two
by transport along evaluation and along the sheafification reflection.

The index type of the formal coproduct is allowed its own universe. The presheaf `F(K)` is the
extension of `uliftYoneda` along `FormalCoproduct.eval`, valued in `Type (max u v w)`; this is
the universe-enlarged form of `FormalCoproduct.yoneda`, and sheafification exists in that
universe for every site. The two van Kampen lemmas are nevertheless stated for an arbitrary
coefficient universe, asking for the coproducts and the left exactness of sheafification as
hypotheses, since a site's own coefficient universe need not be the enlarged one.

The source states its decompositions as equalities of categories. They are given here as
equivalences and isomorphisms bundled with the canonical specification of the forward functor
or of the injections, so that a use site can rewrite with the specification instead of choosing
an unspecified equivalence.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentable

universe u v w t u' v'

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)

/-! ### Van Kampen descent for arbitrary coproducts -/

/-- A coproduct of types, indexed by a type in any universe, is a van Kampen colimit. -/
theorem isVanKampenColimit_types {I : Type w} (F : I → Type v)
    (c : Cocone (Discrete.functor F)) (hc : IsColimit c) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  let F₁ : I → Type v := fun i => F'.obj ⟨i⟩
  have hF₁ : F' = Discrete.functor F₁ := Discrete.functor_ext fun i => rfl
  refine Eq.ndrec (motive := fun {F'} =>
      ∀ (c' : Cocone F') (α : F' ⟶ Discrete.functor F) (f : c'.pt ⟶ c.pt),
        α ≫ c.ι = c'.ι ≫ (Functor.const (Discrete I)).map f →
          NatTrans.Equifibered α →
            (Nonempty (IsColimit c') ↔
              ∀ i : Discrete I, IsPullback (c'.ι.app i) (α.app i) f (c.ι.app i)))
    ?_ (Eq.symm hF₁) c' α f h hα
  intro c' α f h hα
  have hinj (j : I) (z : F'.obj ⟨j⟩) : f (Cofan.inj c' j z) = Cofan.inj c j ((α.app ⟨j⟩) z) := by
    simpa [Cofan.inj] using (ConcreteCategory.congr_hom (NatTrans.congr_app h ⟨j⟩) z).symm
  constructor
  · rintro ⟨hc'⟩ i
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨(NatTrans.congr_app h i).symm,
      fun x y hx => Cofan.inj_injective_of_isColimit hc' i.as hx.1, fun x y hxy => ?_⟩
    obtain ⟨j, z, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc' x
    have htop : Cofan.inj c i.as y = Cofan.inj c j ((α.app ⟨j⟩) z) := hxy.symm.trans (hinj j z)
    obtain ⟨rfl, hz⟩ := (Cofan.inj_apply_eq_iff_of_isColimit hc _ _).1 htop
    exact ⟨z, rfl, hz⟩
  · intro hpb
    apply (Cofan.isColimit_cofanTypes_iff c').1
    apply (CofanTypes.isColimit_iff_bijective_fromSigma _).2
    constructor
    · intro ⟨i, x⟩ ⟨j, y⟩ hxy
      have heq : Cofan.inj c i ((α.app ⟨i⟩) x) = Cofan.inj c j ((α.app ⟨j⟩) y) :=
        (hinj i x).symm.trans ((congrArg f hxy).trans (hinj j y))
      obtain ⟨rfl, hz⟩ := (Cofan.inj_apply_eq_iff_of_isColimit hc _ _).1 heq
      simpa using ((Types.isPullback_iff _ _ _ _).1 (hpb ⟨i⟩)).2.1 x y ⟨hxy, hz.symm⟩
    · intro x
      obtain ⟨i, y, hy⟩ := Cofan.inj_jointly_surjective_of_isColimit hc (f x)
      obtain ⟨z, hz₁, hz₂⟩ := ((Types.isPullback_iff _ _ _ _).1 (hpb ⟨i⟩)).2.2 x y hy.symm
      exact ⟨⟨i, z⟩, hz₁⟩

/-- A coproduct of presheaves of types is a van Kampen colimit: colimits of presheaves are
computed objectwise, and coproducts of types are van Kampen. The coefficient universe is
arbitrary, subject only to having the coproducts in question. -/
theorem isVanKampenColimit_presheafCoproduct {C : Type u} [Category.{v} C]
    {I : Type w} (H : I → Cᵒᵖ ⥤ Type t) [HasColimitsOfShape (Discrete I) (Type t)] :
    IsVanKampenColimit (Limits.Sigma.cocone (Discrete.functor H)) := by
  let G := Discrete.functor H
  let c := Limits.Sigma.cocone G
  apply isVanKampenColimit_of_evaluation G c
  intro X
  let E := (evaluation Cᵒᵖ (Type t)).obj X
  let F₁ := fun i => (H i).obj X
  let e : G ⋙ E ≅ Discrete.functor F₁ := Discrete.natIso fun _ => Iso.refl _
  let c₁ := (Cocone.precompose e.inv).obj (E.mapCocone c)
  have hc₁ := (IsColimit.precomposeInvEquiv e (E.mapCocone c)).symm
    (isColimitOfPreserves E (coproductIsCoproduct' G))
  exact (IsVanKampenColimit.precompose_isIso_iff e.inv).mp (isVanKampenColimit_types F₁ c₁ hc₁)

/-- A coproduct of sheaves of types is a van Kampen colimit, by transporting the presheaf
statement through the sheafification reflection. The coefficient universe is arbitrary, subject
to having the coproducts in question and to sheafification being left exact there. -/
theorem isVanKampenColimit_sheafCoproduct {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {I : Type w}
    [HasSheafify J (Type t)] [HasColimitsOfShape (Discrete I) (Type t)]
    (H : I → Sheaf J (Type t)) :
    IsVanKampenColimit (Limits.Sigma.cocone (Discrete.functor H)) := by
  let G := Discrete.functor H
  let Gr := sheafToPresheaf J (Type t)
  let P := presheafToSheaf J (Type t)
  let H₀ := fun i => (H i).obj
  let F₀ := Discrete.functor H₀
  let e : F₀ ≅ G ⋙ Gr := Discrete.natIso fun _ => Iso.refl _
  let c₀ := Limits.Sigma.cocone F₀
  let c := (Cocone.precompose e.inv).obj c₀
  have hVK := IsVanKampenColimit.precompose_isIso e.inv
    (isVanKampenColimit_presheafCoproduct H₀)
  let adj := sheafificationAdjunction J (Type t)
  have hVK' := IsVanKampenColimit.map_reflective adj hVK
  let θr : Gr ⋙ P ≅ 𝟭 _ := NatIso.ofComponents
    (fun X => asIso (adj.counit.app X)) (fun f => adj.counit.naturality f)
  let θ := G.associator Gr P ≪≫ G.isoWhiskerLeft θr
  let c' := (Cocone.precompose θ.inv).obj (P.mapCocone c)
  have hVK'' := IsVanKampenColimit.precompose_isIso θ.inv hVK'
  let hq := coproductIsCoproduct' G
  exact IsVanKampenColimit.of_iso hVK'' (Cocone.ext (hVK''.isColimit.coconePointUniqueUpToIso hq)
    (fun i => IsColimit.comp_coconePointUniqueUpToIso_hom hVK''.isColimit hq i))

/-! ### The slice category over a van Kampen coproduct -/

/-- A family of objects over the summands of a coproduct, assembled into a single object over
the coproduct. -/
noncomputable def assembleOver {C : Type u} [Category.{v} C] [HasCoproducts C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X)) :
    ((i : I) → Over (X i)) ⥤ Over c.pt where
  obj Z := Over.mk (Limits.Sigma.desc fun i => (Z i).hom ≫ c.ι.app ⟨i⟩)
  map {Z W} f := Over.homMk
    (Limits.Sigma.desc fun i => (f i).left ≫ Limits.Sigma.ι (fun j => (W j).left) i)
  map_id Z := Over.OverMorphism.ext (Limits.Sigma.hom_ext _ _ fun i => by simp)
  map_comp f g := Over.OverMorphism.ext (Limits.Sigma.hom_ext _ _ fun i => by simp)

/-- Each summand of an assembled family is the pullback of the assembled object along the
corresponding injection. -/
theorem isPullback_assembleOver {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasCoproducts C]
    (Z : (i : I) → Over (X i)) (i : Discrete I) :
    IsPullback (Limits.Sigma.ι (fun j => (Z j).left) i.as) (Z i.as).hom
      (Limits.Sigma.desc fun j => (Z j).hom ≫ c.ι.app ⟨j⟩) (c.ι.app i) := by
  let Fz := Discrete.functor fun j => (Z j).left
  let cz := Limits.Sigma.cocone Fz
  let α : Fz ⟶ Discrete.functor X := Discrete.natTrans fun j => (Z j.as).hom
  let f := Limits.Sigma.desc fun j => (Z j).hom ≫ c.ι.app ⟨j⟩
  have hcomm : α ≫ c.ι = cz.ι ≫ (Functor.const (Discrete I)).map f := by
    ext j
    show (Z j.as).hom ≫ c.ι.app j = Limits.Sigma.ι (fun k => (Z k).left) j.as ≫ f
    simp [f]
  exact (hVK cz α f hcomm (.of_discrete α)).mp ⟨coproductIsCoproduct' Fz⟩ i

/-- A compatible family of pullback squares over the summands of a van Kampen coproduct
identifies the coproduct of the pullbacks with the total object, by the morphism assembled from
the first projections. -/
noncomputable def coproductFamilyIsoData {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasCoproducts C]
    (Y : Over c.pt) (P : I → C) (q₁ : (i : I) → P i ⟶ Y.left)
    (q₂ : (i : I) → P i ⟶ X i)
    (hpb : ∀ i : Discrete I, IsPullback (q₁ i.as) (q₂ i.as) Y.hom (c.ι.app i)) :
    {e : (∐ P) ≅ Y.left // e.hom = Limits.Sigma.desc q₁} := by
  let d : Cocone (Discrete.functor P) :=
    ⟨Y.left, Discrete.natTrans fun i => q₁ i.as⟩
  let α : Discrete.functor P ⟶ Discrete.functor X := Discrete.natTrans fun i => q₂ i.as
  have hcomm : α ≫ c.ι = d.ι ≫ (Functor.const (Discrete I)).map Y.hom := by
    ext i
    change q₂ i.as ≫ c.ι.app i = q₁ i.as ≫ Y.hom
    exact (hpb i).w.symm
  let hd : IsColimit d := Classical.choice ((hVK d α Y.hom hcomm (.of_discrete α)).2 hpb)
  let cP := Limits.Sigma.cocone (Discrete.functor P)
  have hcP : IsColimit cP := coproductIsCoproduct' (Discrete.functor P)
  let e := hcP.coconePointUniqueUpToIso hd
  refine ⟨e, hcP.hom_ext fun i => ?_⟩
  change Limits.Sigma.ι P i.as ≫ e.hom = Limits.Sigma.ι P i.as ≫ Limits.Sigma.desc q₁
  rw [Limits.Sigma.ι_desc]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom hcP hd i

/-- The isomorphism of `coproductFamilyIsoData`. -/
noncomputable def coproductFamilyIso {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasCoproducts C]
    (Y : Over c.pt) (P : I → C) (q₁ : (i : I) → P i ⟶ Y.left)
    (q₂ : (i : I) → P i ⟶ X i)
    (hpb : ∀ i : Discrete I, IsPullback (q₁ i.as) (q₂ i.as) Y.hom (c.ι.app i)) :
    (∐ P) ≅ Y.left := (coproductFamilyIsoData c hVK Y P q₁ q₂ hpb).val

/-- `coproductFamilyIso` is the morphism assembled from the first projections. -/
theorem coproductFamilyIso_hom {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasCoproducts C]
    (Y : Over c.pt) (P : I → C) (q₁ : (i : I) → P i ⟶ Y.left)
    (q₂ : (i : I) → P i ⟶ X i)
    (hpb : ∀ i : Discrete I, IsPullback (q₁ i.as) (q₂ i.as) Y.hom (c.ι.app i)) :
    (coproductFamilyIso c hVK Y P q₁ q₂ hpb).hom = Limits.Sigma.desc q₁ :=
  (coproductFamilyIsoData c hVK Y P q₁ q₂ hpb).property

/-- The naturality square for the comparison between the pullbacks of an assembled family and
the family itself. Stated for abstract data so that it can be applied by `exact` to the
naturality goal, whose terms are the same only up to unfolding. -/
lemma isoPullback_inv_naturality {C : Type u} [Category.{v} C] [HasPullbacks C]
    [HasCoproducts C] {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    {Z W : (i : I) → Over (X i)}
    (φ : (∐ fun j => (Z j).left) ⟶ (∐ fun j => (W j).left))
    (g : (j : I) → (Z j).left ⟶ (W j).left) (i : I)
    (hφ : ∀ j, Limits.Sigma.ι (fun k => (Z k).left) j ≫ φ =
      g j ≫ Limits.Sigma.ι (fun k => (W k).left) j)
    (hg : g i ≫ (W i).hom = (Z i).hom)
    {DZ : (∐ fun j => (Z j).left) ⟶ c.pt} {DW : (∐ fun j => (W j).left) ⟶ c.pt}
    (hZ : IsPullback (Limits.Sigma.ι (fun j => (Z j).left) i) (Z i).hom DZ (c.ι.app ⟨i⟩))
    (hW : IsPullback (Limits.Sigma.ι (fun j => (W j).left) i) (W i).hom DW (c.ι.app ⟨i⟩))
    (lift : pullback DZ (c.ι.app ⟨i⟩) ⟶ pullback DW (c.ι.app ⟨i⟩))
    (hlift₁ : lift ≫ pullback.fst DW (c.ι.app ⟨i⟩) = pullback.fst DZ (c.ι.app ⟨i⟩) ≫ φ)
    (hlift₂ : lift ≫ pullback.snd DW (c.ι.app ⟨i⟩) = pullback.snd DZ (c.ι.app ⟨i⟩)) :
    lift ≫ hW.isoPullback.inv = hZ.isoPullback.inv ≫ g i := by
  apply hW.hom_ext
  · simp only [Category.assoc, hW.isoPullback_inv_fst, hlift₁, ← hφ i]
    simp only [← Category.assoc, hZ.isoPullback_inv_fst]
  · simp [hlift₂, hg]

/-- Pulling an assembled family back along the injections recovers the family: each summand of
an assembled family is the pullback of the assembled object along the corresponding injection,
and that identification is natural. -/
noncomputable def assembleOverCompPullbackIso {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasPullbacks C] [HasCoproducts C] :
    assembleOver c ⋙ (Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)) ≅ 𝟭 _ := by
  let B : Over c.pt ⥤ ((i : I) → Over (X i)) :=
    Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)
  let A := assembleOver c
  let ηComponent (Z : (i : I) → Over (X i)) : (A ⋙ B).obj Z ≅ Z :=
    Pi.isoMk fun i => by
      have hpb := isPullback_assembleOver c hVK Z ⟨i⟩
      change (Over.pullback (c.ι.app ⟨i⟩)).obj (A.obj Z) ≅ Z i
      exact Over.isoMk hpb.isoPullback.symm ((Iso.inv_comp_eq _).2 hpb.isoPullback_hom_snd.symm)
  exact NatIso.ofComponents ηComponent (by
        intro Z W f
        ext i
        exact isoPullback_inv_naturality c
          (Limits.Sigma.desc fun j =>
            (f j).left ≫ Limits.Sigma.ι (fun k => (W k).left) j)
          (fun j => (f j).left) i (fun j => Limits.Sigma.ι_desc _ j) (Over.w (f i))
          (isPullback_assembleOver c hVK Z ⟨i⟩) (isPullback_assembleOver c hVK W ⟨i⟩)
          _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))

/-- The slice category over a van Kampen coproduct is the product of the slice categories over
its summands, the equivalence being pullback along the injections componentwise. -/
noncomputable def overCoproductEquivalence {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasPullbacks C] [HasCoproducts C] :
    {e : Over c.pt ≌ ((i : I) → Over (X i)) //
      e.functor = Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)} := by
  let B : Over c.pt ⥤ ((i : I) → Over (X i)) :=
    Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)
  let A := assembleOver c
  have η : A ⋙ B ≅ 𝟭 _ := assembleOverCompPullbackIso c hVK
  let P : Over c.pt → I → C := fun Y i => (B.obj Y i).left
  let q₁ : (Y : Over c.pt) → (i : I) → P Y i ⟶ Y.left :=
    fun Y i => pullback.fst Y.hom (c.ι.app ⟨i⟩)
  let q₂ : (Y : Over c.pt) → (i : I) → P Y i ⟶ X i := fun Y i => (B.obj Y i).hom
  have hpb (Y : Over c.pt) (i : I) :
      IsPullback (q₁ Y i) (q₂ Y i) Y.hom (c.ι.app ⟨i⟩) :=
    IsPullback.of_hasPullback _ _
  let e (Y : Over c.pt) :=
    coproductFamilyIso c hVK Y (P Y) (q₁ Y) (q₂ Y) (fun i => hpb Y i.as)
  let εComponent (Y : Over c.pt) : (B ⋙ A).obj Y ≅ Y :=
    Over.isoMk (e Y) (by
      change (coproductFamilyIso c hVK Y (P Y) (q₁ Y) (q₂ Y)
        (fun i => hpb Y i.as)).hom ≫ Y.hom =
        Limits.Sigma.desc fun i => (B.obj Y i).hom ≫ c.ι.app ⟨i⟩
      rw [coproductFamilyIso_hom]
      refine Limits.Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      exact (hpb Y i).w)
  have ε : B ⋙ A ≅ 𝟭 _ := NatIso.ofComponents εComponent (by
    intro Y Z f
    apply Over.OverMorphism.ext
    change (Limits.Sigma.desc fun i =>
        (B.map f i).left ≫ Limits.Sigma.ι (fun j => (B.obj Z j).left) i) ≫
        (e Z).hom = (e Y).hom ≫ f.left
    rw [coproductFamilyIso_hom, coproductFamilyIso_hom]
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc, Limits.Sigma.ι_desc,
      ← Category.assoc, Limits.Sigma.ι_desc]
    exact pullback.lift_fst _ _ _)
  let : B.IsEquivalence := Functor.IsEquivalence.mk' A ε.symm η
  exact ⟨B.asEquivalence, rfl⟩

/-! ### Sheaves on `C / K` are families of sheaves on the components -/

/-- The comparison functor exchanging an opposite category and a disjoint union. -/
def sigmaOpFunctor {I : Type w} {D : I → Type u} [∀ i, Category.{v} (D i)] :
    (Opposite (Σ i, D i)) ⥤ (Σ i, Opposite (D i)) where
  obj X := ⟨X.unop.1, .op X.unop.2⟩
  map {X Y} f := by
    rcases X with ⟨⟨i, X⟩⟩
    rcases Y with ⟨⟨j, Y⟩⟩
    change (⟨i, Opposite.op X⟩ : Σ i, Opposite (D i)) ⟶ ⟨j, Opposite.op Y⟩
    rcases f.unop with ⟨g⟩
    exact CategoryTheory.Sigma.SigmaHom.mk g.op
  map_id := by
    rintro ⟨⟨i, X⟩⟩
    rfl
  map_comp := by
    rintro ⟨⟨i, X⟩⟩ ⟨⟨j, Y⟩⟩ ⟨⟨k, Z⟩⟩ f g
    cases hf : f.unop with
    | mk f' =>
      cases hg : g.unop with
      | mk g' =>
        have hf' : f = Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk f') := by
          apply Quiver.Hom.unop_inj
          simpa using hf
        have hg' : g = Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk g') := by
          apply Quiver.Hom.unop_inj
          simpa using hg
        subst f
        subst g
        rfl

/-- The presheaf on `C / K` assembled from a family of sheaves on the component slices. -/
def componentPresheaf (A : Type u') [Category.{v'} A]
    (F : ∀ i : K.I, Sheaf (J.over (K.obj i)) A) :
    (ComponentOver K)ᵒᵖ ⥤ A :=
  sigmaOpFunctor ⋙ CategoryTheory.Sigma.desc (fun i => (F i).obj)

/-- The assembled presheaf is a sheaf for the componentwise topology. -/
lemma componentPresheaf_isSheaf (A : Type u') [Category.{v'} A]
    (F : ∀ i : K.I, Sheaf (J.over (K.obj i)) A) :
    Presheaf.IsSheaf (componentwiseTopology J K) (componentPresheaf J K A F) := by
  refine fun E => isSheaf_componentwise J _ fun i X S hS x hx => ?_
  exact (F i).property E S hS (fun _ f hf => x f hf)
    (fun _ _ _ g₁ g₂ _ _ h₁ h₂ e => hx g₁ g₂ h₁ h₂ e)

/-- Restriction of a sheaf on `C / K` to the component slices. -/
def restrictSheaf (A : Type u') [Category.{v'} A] :
    Sheaf (componentwiseTopology J K) A ⥤
      ((i : K.I) → Sheaf (J.over (K.obj i)) A) where
  obj F i := ⟨(CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).op ⋙ F.obj,
    by
      have := incl_isContinuous J K i
      exact CategoryTheory.Functor.op_comp_isSheaf
        (F := CategoryTheory.Sigma.incl
          (C := fun i : K.I => Over (K.obj i)) i)
        (J := J.over (K.obj i)) (K := componentwiseTopology J K) F⟩
  map f i := ObjectProperty.homMk <| CategoryTheory.Functor.whiskerLeft
    (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).op f.hom
  map_id F := by
    funext i
    apply Sheaf.hom_ext
    simp
  map_comp f g := by
    funext i
    apply Sheaf.hom_ext
    simp

/-- A morphism of families of sheaves, assembled into a morphism of the assembled presheaves. -/
def componentNatTrans (A : Type u') [Category.{v'} A]
    {F G : ∀ i : K.I, Sheaf (J.over (K.obj i)) A} (f : F ⟶ G) :
    componentPresheaf J K A F ⟶ componentPresheaf J K A G :=
  CategoryTheory.Functor.whiskerLeft sigmaOpFunctor
    (CategoryTheory.Sigma.natTrans fun i => (f i).hom)

/-- A family of sheaves on the component slices, assembled into a sheaf on `C / K`. -/
def assembleSheaf (A : Type u') [Category.{v'} A] :
    ((i : K.I) → Sheaf (J.over (K.obj i)) A) ⥤
      Sheaf (componentwiseTopology J K) A where
  obj F := ⟨componentPresheaf J K A F, componentPresheaf_isSheaf J K A F⟩
  map f := ObjectProperty.homMk (componentNatTrans J K A f)
  map_id F := by
    apply Sheaf.hom_ext
    ext ⟨⟨i, X⟩⟩
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    ext ⟨⟨i, X⟩⟩
    rfl

/-- Restricting an assembled family of sheaves recovers the family. -/
def restrictAssembleIso (A : Type u') [Category.{v'} A]
    (F : ∀ i : K.I, Sheaf (J.over (K.obj i)) A) :
    (restrictSheaf J K A).obj ((assembleSheaf J K A).obj F) ≅ F :=
  CategoryTheory.Pi.isoMk fun i => ObjectProperty.isoMk (Presheaf.IsSheaf (J.over (K.obj i))) <|
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      change (F i).obj.map f ≫ 𝟙 _ = 𝟙 _ ≫ (F i).obj.map f
      simp)

/-- Sheaves on `C / K` are families of sheaves on the component slices, the equivalence being
restriction along the component inclusions. -/
noncomputable def formalCoproductSliceSheavesEquivalenceFunctor
    (A : Type u') [Category.{v'} A] :
    Sheaf (componentwiseTopology J K) A ≌
      ((i : K.I) → Sheaf (J.over (K.obj i)) A) := by
  let R := restrictSheaf J K A
  let A' := assembleSheaf J K A
  let : R.Faithful := ⟨fun {F G} f g h => by
    apply Sheaf.hom_ext
    ext X
    rcases X with ⟨⟨i, X⟩⟩
    exact congrArg (fun k => k.hom.app (Opposite.op X)) (congrFun h i)⟩
  let : R.Full := ⟨fun {F G} f => ⟨ObjectProperty.homMk {
    app := fun X => by
      rcases X with ⟨⟨i, X⟩⟩
      exact (f i).hom.app (Opposite.op X)
    naturality := by
      rintro ⟨⟨i, X⟩⟩ ⟨⟨j, Y⟩⟩ g
      cases hg : g.unop with
      | mk g' =>
        have hg' : g = Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
            (C := fun i : K.I => Over (K.obj i)) g') := by
          apply Quiver.Hom.unop_inj
          simpa using hg
        subst g
        exact (f i).hom.naturality g'.op }, by
    funext i
    apply Sheaf.hom_ext
    ext X
    rfl⟩⟩
  let : R.EssSurj := ⟨fun F => ⟨A'.obj F, ⟨restrictAssembleIso J K A F⟩⟩⟩
  let : R.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact R.asEquivalence

/-- Sheaves on `C / K` are families of sheaves on the component slices. The equivalence
restricts the underlying presheaf along each component inclusion, naturally in the sheaf. -/
noncomputable def formalCoproductSliceSheavesEquivalence
    (A : Type u') [Category.{v'} A] :
    { e : Sheaf (componentwiseTopology J K) A ≌
        ((i : K.I) → Sheaf (J.over (K.obj i)) A) //
      ∀ i : K.I, Nonempty
        (e.functor ⋙ Pi.eval (fun i : K.I ↦ Sheaf (J.over (K.obj i)) A) i ⋙
            sheafToPresheaf (J.over (K.obj i)) A ≅
          sheafToPresheaf (componentwiseTopology J K) A ⋙
            (Functor.whiskeringLeft (Over (K.obj i))ᵒᵖ
              (ComponentOver K)ᵒᵖ A).obj
                (CategoryTheory.Sigma.incl (C := fun i : K.I ↦ Over (K.obj i)) i).op) } :=
  ⟨formalCoproductSliceSheavesEquivalenceFunctor J K A, fun _ => ⟨Iso.refl _⟩⟩

/-! ### The sheaf associated to a semi-representable object -/

/-- Sheafifying the semi-representable presheaf attached to `K` gives the coproduct of the
sheafifications of the representables `K.obj i`, and the isomorphism carries the sheafified
presheaf injections to the sheaf coproduct injections. -/
noncomputable def sheafificationFormalCoproductIso :
    { e :
        (presheafToSheaf J (Type max u v w)).obj
            (((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type max u v w)).obj
              uliftYoneda.{max u w}).obj K) ≅
          ∐ (fun i : K.I ↦ (presheafToSheaf J (Type max u v w)).obj
            (uliftYoneda.{max u w}.obj (K.obj i))) //
      ∀ i : K.I,
        (presheafToSheaf J (Type max u v w)).map
            (Limits.Sigma.ι (fun i : K.I ↦ uliftYoneda.{max u w}.obj (K.obj i)) i) ≫
          e.hom =
        Limits.Sigma.ι (fun i : K.I ↦ (presheafToSheaf J (Type max u v w)).obj
          (uliftYoneda.{max u w}.obj (K.obj i))) i } := by
  classical
  let H₀ : K.I → Cᵒᵖ ⥤ Type (max u v w) :=
    fun i => uliftYoneda.{max u w}.obj (K.obj i)
  let F : Discrete K.I ⥤ Cᵒᵖ ⥤ Type (max u v w) := Discrete.functor H₀
  let H : K.I → Sheaf J (Type (max u v w)) :=
    fun i => (presheafToSheaf J (Type (max u v w))).obj (H₀ i)
  let c : Cocone F := Limits.Sigma.cocone F
  let P := presheafToSheaf J (Type (max u v w))
  let G : Discrete K.I ⥤ Sheaf J (Type (max u v w)) := F ⋙ P
  let d := P.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves P (coproductIsCoproduct' F)
  let q : Cocone G := ⟨∐ H, Discrete.natTrans fun i => Limits.Sigma.ι H i.as⟩
  have hq : IsColimit q := by
    apply IsColimit.ofIsoColimit (coproductIsCoproduct' G)
    exact Cocone.ext (Iso.refl _) (by
      intro i
      simp [q, Limits.Sigma.cocone, H, G, F, H₀, P])
  exact ⟨hd.coconePointUniqueUpToIso hq,
    fun i => IsColimit.comp_coconePointUniqueUpToIso_hom hd hq ⟨i⟩⟩

/-- Pullback along the sheafified coproduct injections decomposes the slice category over the
sheaf associated to `K` as the product of the slice categories over its components. -/
noncomputable def sheavesOverSheafificationFormalCoproductEquivalence :
    { e :
        Over ((presheafToSheaf J (Type max u v w)).obj
          (((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type max u v w)).obj
            uliftYoneda.{max u w}).obj K)) ≌
          ((i : K.I) → Over ((presheafToSheaf J (Type max u v w)).obj
            (uliftYoneda.{max u w}.obj (K.obj i)))) //
      e.functor = Functor.pi' (fun i : K.I ↦
        Over.pullback ((presheafToSheaf J (Type max u v w)).map
          (Limits.Sigma.ι (fun i : K.I ↦ uliftYoneda.{max u w}.obj (K.obj i)) i))) } := by
  classical
  let H₀ : K.I → Cᵒᵖ ⥤ Type (max u v w) :=
    fun i => uliftYoneda.{max u w}.obj (K.obj i)
  let X₀ : Cᵒᵖ ⥤ Type (max u v w) :=
    ((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max u v w))).obj
      uliftYoneda.{max u w}).obj K
  let Psh := presheafToSheaf J (Type (max u v w))
  let H : K.I → Sheaf J (Type (max u v w)) :=
    fun i => Psh.obj (H₀ i)
  let d : Cocone (Discrete.functor H) :=
    ⟨∐ H, Discrete.natTrans fun i => Limits.Sigma.ι H i.as⟩
  have hd : IsColimit d := by
    apply IsColimit.ofIsoColimit (coproductIsCoproduct' (Discrete.functor H))
    exact Cocone.ext (Iso.refl _) (by intro i; simp [d, Limits.Sigma.cocone])
  have hVK₀ : IsVanKampenColimit (Limits.Sigma.cocone (Discrete.functor H)) :=
    isVanKampenColimit_sheafCoproduct J H
  let eColim := (coproductIsCoproduct' (Discrete.functor H)).coconePointUniqueUpToIso hd
  have hVK : IsVanKampenColimit d := hVK₀.of_iso (Cocone.ext eColim (by
    intro i
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct' (Discrete.functor H)) hd i))
  let sl := overCoproductEquivalence d hVK
  let hSheaf := sheafificationFormalCoproductIso J K
  let e₀ := hSheaf.val
  let A : Over (Psh.obj X₀) ⥤ Over d.pt := Over.pullback e₀.inv
  let B := Functor.pi' (fun i : K.I => Over.pullback (d.ι.app ⟨i⟩))
  let E := A ⋙ B
  let G : Over (Psh.obj X₀) ⥤ ((i : K.I) → Over (Psh.obj
      (H₀ i))) := Functor.pi' (fun i : K.I => Over.pullback (Psh.map (Limits.Sigma.ι H₀ i)))
  have hPB (i : K.I) :
      Over.pullback e₀.inv ⋙ Over.pullback (Limits.Sigma.ι H i) ≅
        Over.pullback (Psh.map (Limits.Sigma.ι H₀ i)) :=
    (Over.pullbackComp (Limits.Sigma.ι H i) e₀.inv).symm ≪≫ eqToIso (congrArg
      (fun f => Over.pullback f) ((Iso.eq_comp_inv e₀).mpr (hSheaf.property i))).symm
  have hEB : E ≅ G := NatIso.ofComponents (fun Y => Pi.isoMk fun i => (hPB i).app Y)
    fun f => funext fun i => (hPB i).hom.naturality f
  let mapE := Over.mapIso (asIso e₀.inv)
  let : (Over.map e₀.inv).IsEquivalence := mapE.isEquivalence_functor
  let : (Over.map e₀.inv).Full := mapE.isEquivalence_functor.full
  let : (Over.map e₀.inv).Faithful := mapE.isEquivalence_functor.faithful
  let adj := Over.mapPullbackAdj e₀.inv
  let : ∀ Y : Over d.pt, IsIso (adj.unit.app Y) := fun Y => inferInstance
  let : A.IsEquivalence := adj.toEquivalence.isEquivalence_inverse
  have hB : sl.val.functor = B := sl.property
  let : B.IsEquivalence := hB ▸ sl.val.isEquivalence_functor
  let : E.IsEquivalence := inferInstance
  let : G.IsEquivalence := Functor.isEquivalence_of_iso hEB
  exact ⟨G.asEquivalence, rfl⟩

/-- **Assembling is the quasi-inverse.** The functor assembling a family of objects over the
summands of a van Kampen coproduct into one object over the coproduct is an equivalence: it is
inverse to componentwise pullback along the injections, which is `overCoproductEquivalence`. -/
theorem isEquivalence_assembleOver {C : Type u} [Category.{v} C]
    {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X))
    (hVK : IsVanKampenColimit c) [HasPullbacks C] [HasCoproducts C] :
    (assembleOver c).IsEquivalence := by
  let B : Over c.pt ⥤ ((i : I) → Over (X i)) :=
    Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)
  have hB : B.IsEquivalence := by
    have h := overCoproductEquivalence c hVK
    have := h.val.isEquivalence_functor
    rw [show B = Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩) from rfl, ← h.property]
    infer_instance
  have hiso : assembleOver c ≅ B.inv :=
    (Functor.rightUnitor (assembleOver c)).symm ≪≫
      Functor.isoWhiskerLeft (assembleOver c) B.asEquivalence.unitIso ≪≫
      (Functor.associator (assembleOver c) B B.inv).symm ≪≫
      Functor.isoWhiskerRight (assembleOverCompPullbackIso c hVK) B.inv ≪≫
      Functor.leftUnitor _
  exact Functor.isEquivalence_of_iso hiso.symm

end CategoryTheory.SemiRepresentable

end
