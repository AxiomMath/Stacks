module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# The descent construction for a simplicial site (Stacks 09WF)

Stacks 09WF describes the sheaves on the total site of a simplicial-site situation by their
restrictions to the components together with the transitions between them. The functor from
total-site sheaves to systems of restrictions is
`CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor`, which is fully faithful
(`CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor_full` and
`CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor_faithful`). This file supplies the
other half of the lemma: every system of sheaves on the components comes from a
sheaf on the total site. That is the descent construction, and with it the equivalence of
Stacks 09WF is proved.

The sheaf is built fibre by fibre. A system assigns a sheaf to every simplicial degree and a
transition map to every simplex map; transposing the transitions into direct-image form turns
that data into exactly what a functor out of the total category needs, and the unit and cocycle
laws of the system become the two coherence hypotheses of the construction of such a functor
from fibrewise data. The resulting presheaf is a sheaf because the total topology is generated
by the covering families of the individual fibres, and the restriction of the presheaf to a
fibre is the component sheaf of the system.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.systemPresheaf`: the presheaf on the total site
  underlying a system, in both cases of the situation.
* `CategoryTheory.SimplicialSiteSituation.systemTotalSheaf`: that presheaf, with its sheaf
  condition, as a sheaf on the total site.
* `CategoryTheory.SimplicialSiteSituation.restrictIso`: its restriction to the component in a
  given simplicial degree is the component sheaf of the system.
* `CategoryTheory.SimplicialSiteSituation.restrictSystemTotalSheafIso`: the system of
  restrictions of that sheaf is the given system.
* `CategoryTheory.SimplicialSiteSituation.totalPresentation`: **Stacks 09WF.** The presentation
  of the sheaves on the total site as systems on the components, with no hypotheses; its
  `totalEquivalence` field is the equivalence of the tag.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.functorFrom_map_ιNatTrans_app` and
  `CategoryTheory.Grothendieck.functorFromOfEq_map_ιNatTrans_app`: a functor built from
  fibrewise data sends a Cartesian lift to the transition of the family.
* `CategoryTheory.Grothendieck.ιCompFunctorFromOfEq`: the restriction of such a functor to a
  fibre is the functor the construction was given there.
* `CategoryTheory.Functor.leftOpIso`: `Functor.leftOp` of a natural isomorphism.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrictSystemFunctor_essSurj`: the functor taking a
  total-site sheaf to its system of restrictions is essentially surjective. This is the descent
  construction.
* `CategoryTheory.SimplicialSiteSituation.totalPresentation_transition_restriction`: the
  transitions of the system attached to a total-site sheaf are the inverse-image transitions of
  its restrictions.
* `CategoryTheory.Presieve.isSheafFor_map`: a presheaf which is a sheaf for a presieve after
  restriction along a functor is a sheaf for the image of that presieve.
* `CategoryTheory.isSheaf_topologyOfCoverings`: a presheaf which is a sheaf for the generating
  covering families of a family-based site is a sheaf for the topology they generate.
* `CategoryTheory.cocontinuousPushforwardId_homEquiv_eqToHom` and
  `CategoryTheory.cocontinuousTranspose_comp_ofEq`: the unit and cocycle laws for the transposes
  of the direct images along cocontinuous site functors.

## Implementation notes

The two cases of the situation need different constructions, because the total category is the
contravariant `CoGrothendieck` construction in case (A) and the covariant `Grothendieck`
construction in case (B). The two are assembled by a match on the case, exactly as
`CategoryTheory.SimplicialSiteSituation.restrictTransition` is.

In both cases the fibrewise data of the presheaf is the *direct-image* transition of the system,
transposed: in case (A) the direct image is precomposition and the transposition is trivial,
while in case (B) it is a right Kan extension, and the transition has to be passed back through
the Kan-extension adjunction before it is a family of maps on sections. The unit and cocycle
laws for those transposes are the two general lemmas
`CategoryTheory.cocontinuousPushforwardId_homEquiv_eqToHom` and
`CategoryTheory.cocontinuousTranspose_comp_ofEq`, both stated with no situation in them.

The target of the fibrewise functors is `(Type u)ᵒᵖ`, so that `Functor.leftOp` of the functor
out of the total category is a presheaf on it; the fibrewise functors are therefore
`Functor.rightOp` of the component sheaves, and the transitions are `NatTrans.rightOp` of their
transposes. Those two constructions are given names, rather than written out, because their
declared types are the ones on which the laws below are stated: written out, the goals are no
longer type-correct at the `implicit` transparency level — the component category of a degree
is only definitionally the value of the diagram of categories there — and from that point `rw`
and `simp only` stop firing.

The sheaf condition is the generating-presieve criterion. In case (A) the total coverage is a
`Precoverage` with pullbacks and stable under base change, so
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange` reduces the
condition to the generating families; in case (B) the covering families are family-based, and
the same reduction is `CategoryTheory.isSheaf_topologyOfCoverings`. Either way the generating
families are the images of the fibrewise ones under a component inclusion, and
`CategoryTheory.Presieve.isSheafFor_map` reduces the condition on such an image to the condition
on the fibrewise family for the restricted presheaf — which the identification of that
restriction with the component sheaf supplies.

Essential surjectivity is then the isomorphism of the system of restrictions of the constructed
sheaf with the given system. Its components are the fibrewise identifications, which are the
identity on sections; the one law to check is that they carry the transitions of the
restrictions to the transitions of the system. That law is proved in *direct-image* form, as
full faithfulness was, and transported to the inverse images by the topos adjunction of the
transition morphism, because restriction along a cross-fibre arrow is a direct-image statement.

The compatibility of the transitions of a system with the fibrewise restrictions is stated for
`CategoryTheory.SimplicialSiteSituation.totalPresentation` and not for an arbitrary
`SimplicialSheafPresentation`: a presentation constrains its component identifications only by
naturality in the sheaf, so the compatibility is extra data there, whereas for this presentation
the identifications are the identity and the statement is the round trip through `AsSmall`.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe v₁ u₁ v₂ u₂ v u

namespace CategoryTheory

/-- Taking `Functor.rightOp` of a transport along an equality of presheaves is the transport
along the opposite equality of their `Functor.rightOp`s. -/
theorem NatTrans.rightOp_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A B : Cᵒᵖ ⥤ D} (h : A = B) :
    NatTrans.rightOp (eqToHom h) = eqToHom (congrArg Functor.rightOp h.symm) := by
  subst h; rfl

/-- Taking `Functor.rightOp` commutes with whiskering on the left. -/
theorem NatTrans.rightOp_whiskerLeft {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u} [Category.{v} E] (k : C ⥤ D) {A B : Dᵒᵖ ⥤ E} (β : A ⟶ B) :
    NatTrans.rightOp (Functor.whiskerLeft k.op β) =
      Functor.whiskerLeft k (NatTrans.rightOp β) := rfl

/-- `Functor.leftOp` of a natural isomorphism, reversing its direction. -/
def Functor.leftOpIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A B : C ⥤ Dᵒᵖ} (e : A ≅ B) : B.leftOp ≅ A.leftOp where
  hom := NatTrans.leftOp e.hom
  inv := NatTrans.leftOp e.inv
  hom_inv_id := by rw [← NatTrans.leftOp_comp, e.inv_hom_id, NatTrans.leftOp_id]
  inv_hom_id := by rw [← NatTrans.leftOp_comp, e.hom_inv_id, NatTrans.leftOp_id]

/-- A presheaf whose restriction along a functor is a sheaf for a presieve is a sheaf for the
image of that presieve. No hypothesis on the functor is needed: a family of elements for the
image presieve restricts to one for the presieve, compatibly, and an amalgamation of the
restricted family amalgamates the original one because every arrow of the image presieve *is*
the image of an arrow of the presieve. -/
theorem Presieve.isSheafFor_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (ι : C ⥤ D) (P : Dᵒᵖ ⥤ Type v) {X : C} (R : Presieve X)
    (h : Presieve.IsSheafFor (ι.op ⋙ P) R) : Presieve.IsSheafFor P (R.map ι) := by
  intro x hx
  let y : Presieve.FamilyOfElements (ι.op ⋙ P) R :=
    fun _ g hg => x (ι.map g) (Presieve.map_map hg)
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact hx (ι.map g₁) (ι.map g₂) _ _ (by rw [← ι.map_comp, ← ι.map_comp, hcomm])
  obtain ⟨t, ht, huniq⟩ := h y hy
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    obtain ⟨Z, hZ, g, hg, hfg⟩ := Presieve.map_iff.mp hf
    subst hZ
    rw [eqToHom_refl, Category.id_comp] at hfg
    subst hfg
    exact ht g hg
  · intro t' ht'
    exact huniq t' fun {Z} g hg => ht' (ι.map g) (Presieve.map_map hg)

/-- The form of `CategoryTheory.Presieve.isSheafFor_map` for the presieve of a covering
family. -/
theorem Presieve.isSheafFor_presieve₀_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (ι : C ⥤ D) (P : Dᵒᵖ ⥤ Type v) {X : C} (E : PreZeroHypercover.{u} X)
    (h : Presieve.IsSheafFor (ι.op ⋙ P) E.presieve₀) :
    Presieve.IsSheafFor P (E.map ι).presieve₀ := by
  rw [PreZeroHypercover.presieve₀_map]
  exact Presieve.isSheafFor_map ι P _ h

/-- The general cocontinuous ingredient of the unit law for transposed direct images. If a
cocontinuous site functor is the identity, then the transpose of a transport of a sheaf along
that identity cancels the identification of its direct image with the identity functor. -/
theorem cocontinuousPushforwardId_homEquiv_eqToHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {w : C ⥤ C} [w.IsCocontinuous J J] (hw : w = 𝟭 C)
    (X : Sheaf J (Type u)) (hX : w.op ⋙ X.obj = X.obj) :
    (w.op.ranAdjunction (Type u)).homEquiv X.obj X.obj (eqToHom hX) ≫
        ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J J hw ≪≫
          (((𝟭 C).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
            (Functor.sheafPushforwardContinuousId (Type u) J)).rightAdjointUniq
            Adjunction.id).hom.app X).hom = 𝟙 _ := by
  subst hw
  have h : hX = rfl := rfl
  subst h
  rw [eqToHom_refl, SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl,
    show (((𝟭 C).op.ranAdjunction (Type u)).homEquiv X.obj X.obj) (𝟙 _) =
      ((𝟭 C).op.ranAdjunction (Type u)).unit.app X.obj from Adjunction.homEquiv_id _ _,
    Iso.refl_trans, rightAdjointUniq_sheafAdjunctionCocontinuous_id_hom_app_hom,
    Adjunction.rightAdjointUniq_id_hom_app]
  exact Adjunction.left_triangle_components ((𝟭 C).op.ranAdjunction (Type u)) X.obj

/-- The transpose of a composite along the Kan extension of a composite of functors: it is the
composite of the two transposes, compared by the compositor `ranOpCompIso` of the two Kan
extensions. This is the presheaf-level form of the cocycle law for transposed direct images, and
it takes the two transposed families as arbitrary natural transformations. -/
theorem ranOp_homEquiv_whiskerLeft_comp {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u}
    [SmallCategory C₁] {C₂ : Type u} [SmallCategory C₂] (u : C₀ ⥤ C₁) (v : C₁ ⥤ C₂)
    (P₀ : C₀ᵒᵖ ⥤ Type u) (P₁ : C₁ᵒᵖ ⥤ Type u) (P₂ : C₂ᵒᵖ ⥤ Type u)
    (a : u.op ⋙ P₁ ⟶ P₀) (b : v.op ⋙ P₂ ⟶ P₁) :
    ((u ⋙ v).op.ranAdjunction (Type u)).homEquiv P₂ P₀
          (Functor.whiskerLeft u.op b ≫ a) ≫
        (ranOpCompIso u v).hom.app P₀ =
      (v.op.ranAdjunction (Type u)).homEquiv P₂ P₁ b ≫
        v.op.ran.map ((u.op.ranAdjunction (Type u)).homEquiv P₁ P₀ a) := by
  have hU : ((u.op.ranAdjunction (Type u)).homEquiv (v.op ⋙ P₂) P₀)
        (Functor.whiskerLeft u.op b ≫ a) =
      b ≫ ((u.op.ranAdjunction (Type u)).homEquiv P₁ P₀) a := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((u.op.ranAdjunction (Type u)).unit.naturality b).symm
  rw [ranOpCompIso_def]
  simp only [Functor.op_comp_eq]
  rw [Adjunction.homEquiv_comp_rightAdjointUniq_hom_app, Adjunction.comp_homEquiv]
  refine Eq.trans (congrArg ((v.op.ranAdjunction (Type u)).homEquiv P₂
    (u.op.ran.obj P₀)) hU) ?_
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The general cocontinuous ingredient of the cocycle law for transposed direct images, in the
form a situation-level law consumes: the composite site functor is named by a variable,
identified with the composite by a hypothesis, and the transport of the direct images along that
identification appears as the last factor. -/
theorem cocontinuousTranspose_comp_ofEq
    {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u} [SmallCategory C₁] {C₂ : Type u}
    [SmallCategory C₂]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    {u : C₀ ⥤ C₁} {v : C₁ ⥤ C₂} {w : C₀ ⥤ C₂}
    [u.IsCocontinuous J₀ J₁] [v.IsCocontinuous J₁ J₂] [w.IsCocontinuous J₀ J₂]
    [(u ⋙ v).IsCocontinuous J₀ J₂]
    (X₀ : Sheaf J₀ (Type u)) (P₁ : C₁ᵒᵖ ⥤ Type u) (P₂ : C₂ᵒᵖ ⥤ Type u)
    (a : u.op ⋙ P₁ ⟶ X₀.obj) (b : v.op ⋙ P₂ ⟶ P₁) {cw : w.op ⋙ P₂ ⟶ X₀.obj}
    (hw : u ⋙ v = w)
    (hc : cw = eqToHom (congrArg (fun k : C₀ ⥤ C₂ => k.op ⋙ P₂) hw.symm) ≫
      Functor.whiskerLeft u.op b ≫ a) :
    (w.op.ranAdjunction (Type u)).homEquiv P₂ X₀.obj cw =
      (v.op.ranAdjunction (Type u)).homEquiv P₂ P₁ b ≫
        v.op.ran.map ((u.op.ranAdjunction (Type u)).homEquiv P₁ X₀.obj a) ≫
          (((sheafPushforwardCocontinuousCompIso J₀ J₁ J₂ u v).inv.app X₀).hom ≫
            ((SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J₀ J₂
              hw).hom.app X₀).hom) := by
  subst hw
  subst hc
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl, eqToHom_refl _ rfl,
    Category.id_comp]
  simp only [Iso.refl_hom, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom]
  rw [sheafPushforwardCocontinuousCompIso_inv_app_hom]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (Iso.eq_comp_inv ((ranOpCompIso u v).app X₀.obj)).mpr
    (ranOp_homEquiv_whiskerLeft_comp u v X₀.obj P₁ P₂ a b)

namespace Grothendieck

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{v₂, u₂}} {E : Type u} [Category.{v} E]
variable (fib : ∀ c, F.obj c ⥤ E)
  (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
  (hom_id : ∀ c, hom (𝟙 c) = eqToHom (fib_map_id_eq fib c))
  (hom_comp : ∀ (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (fib_map_comp_eq fib f g))


/-- The action of `CategoryTheory.Grothendieck.functorFromOfEq` on a morphism of the total
category. -/
theorem functorFromOfEq_map (fib : ∀ c, F.obj c ⥤ E)
    (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
    (hom_id : ∀ c, hom (𝟙 c) = eqToHom (fib_map_id_eq fib c))
    (hom_comp : ∀ (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
      hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (fib_map_comp_eq fib f g))
    {X Y : Grothendieck F} (f : X ⟶ Y) :
    (functorFromOfEq fib hom hom_id hom_comp).map f =
      (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber := rfl

/-- A functor out of the Grothendieck construction built from fibrewise data sends a Cartesian
lift of a base arrow to the transition of the family at that arrow. -/
theorem functorFromOfEq_map_ιNatTrans_app (fib : ∀ c, F.obj c ⥤ E)
    (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
    (hom_id : ∀ c, hom (𝟙 c) = eqToHom (fib_map_id_eq fib c))
    (hom_comp : ∀ (c₁ c₂ c₃ : C) (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
      hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (fib_map_comp_eq fib f g))
    {X Y : C} (f : X ⟶ Y) (a : F.obj X) :
    (functorFromOfEq fib hom hom_id hom_comp).map ((ιNatTrans f).app a) = (hom f).app a :=
  (functorFromOfEq_map fib hom hom_id hom_comp _).trans
    ((congrArg (fun t => (hom f).app a ≫ t)
      (CategoryTheory.Functor.map_id (fib Y) _)).trans (Category.comp_id _))

/-- The fibre inclusion composed with `CategoryTheory.Grothendieck.functorFromOfEq` is the
functor the construction was given on that fibre. This is the counterpart, for the form of the
construction whose coherences are stated through named equalities, of Mathlib's
`CategoryTheory.Grothendieck.ιCompFunctorFrom`. -/
def ιCompFunctorFromOfEq (c : C) :
    ι F c ⋙ functorFromOfEq fib hom hom_id hom_comp ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Functor.comp_map, functorFromOfEq, Grothendieck.ι, hom_id, eqToHom_app,
      Iso.refl_hom, Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_comp,
      eqToHom_map]
    simp)

end Grothendieck


namespace Pseudofunctor.CoGrothendieck

/-- A functor out of the contravariant Grothendieck construction built from fibrewise data
sends a Cartesian lift of a base arrow to the transition of the family at that arrow. -/
theorem functorFrom_map_ιNatTrans_app {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}} {E : Type u} [Category.{v} E]
    (fib : ∀ S : 𝒮, F.obj ⟨Opposite.op S⟩ ⥤ E)
    (hom : ∀ {R S : 𝒮} (f : R ⟶ S), (F.map f.op.toLoc).toFunctor ⋙ fib R ⟶ fib S)
    (hom_id : ∀ S : 𝒮, hom (𝟙 S) =
      Functor.whiskerRight (F.mapId ⟨Opposite.op S⟩).hom.toNatTrans (fib S))
    (hom_comp : ∀ {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T), hom (f ≫ g) =
      Functor.whiskerRight (F.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans (fib R) ≫
        Functor.whiskerLeft (F.map g.op.toLoc).toFunctor (hom f) ≫ hom g)
    {R S : 𝒮} (f : R ⟶ S) (a : F.obj ⟨Opposite.op S⟩) :
    (functorFrom fib hom hom_id hom_comp).map ((ιNatTrans F f).app a) = (hom f).app a :=
  (functorFrom_map fib hom hom_id hom_comp _).trans
    ((congrArg (fun t => t ≫ (hom f).app a)
      (CategoryTheory.Functor.map_id (fib R) _)).trans (Category.id_comp _))

end Pseudofunctor.CoGrothendieck

/-- A presheaf which satisfies the sheaf condition for every generating covering family of a
family-based site is a sheaf for the topology those families generate. The base-change axiom of
the site is what turns the generating families into a `CategoryTheory.Coverage`, for which the
criterion is Mathlib's `CategoryTheory.Presieve.isSheaf_coverage`. -/
theorem isSheaf_topologyOfCoverings {C : Type u} [SmallCategory C]
    {Cov : Covering.{u, u, u} C → Prop} (hCov : IsSite Cov) (P : Cᵒᵖ ⥤ Type u)
    (h : ∀ (X : C) (E : PreZeroHypercover.{u} X), Cov ⟨X, E⟩ →
      Presieve.IsSheafFor P E.presieve₀) :
    Presieve.IsSheaf (topologyOfCoverings Cov) P := by
  let K : Coverage C :=
    { coverings := fun X => {R | ∃ E : PreZeroHypercover X, Cov ⟨X, E⟩ ∧ E.presieve₀ = R}
      pullback := by
        intro X Y f R hR
        obtain ⟨E, hE, rfl⟩ := hR
        obtain ⟨Q, p₁, p₂, hpb, hCov'⟩ := hCov.2.2 ⟨X, E⟩ hE Y f
        refine ⟨(⟨E.I₀, Q, p₂⟩ : PreZeroHypercover Y).presieve₀,
          ⟨⟨E.I₀, Q, p₂⟩, hCov', rfl⟩, ?_⟩
        intro Z g hg
        cases hg with
        | mk i => exact ⟨E.X i, p₁ i, E.f i, ⟨i⟩, (hpb i).w⟩ }
  have hK : K.toGrothendieck = topologyOfCoverings Cov := by
    rw [← Coverage.toGrothendieck_toPrecoverage K]
    rfl
  rw [← hK, Presieve.isSheaf_coverage]
  intro X R hR
  obtain ⟨E, hE, rfl⟩ := hR
  exact h X E hE

/-- A presheaf isomorphic to a sheaf is a sheaf for any presieve generating a covering sieve. -/
private theorem isSheafFor_of_iso_sheaf {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (X : Sheaf J (Type u)) {Q : Cᵒᵖ ⥤ Type u} (e : Q ≅ X.obj) {Y : C} (T : Presieve Y)
    (hT : Sieve.generate T ∈ J Y) : Presieve.IsSheafFor Q T :=
  Presieve.isSheafFor_iso e.symm ((Presieve.isSheafFor_iff_generate T).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mp X.property _ hT))

namespace SimplicialSiteSituation

/-- In case (B), the inverse of the direct-image unit comparison is the transpose, along the
Kan-extension adjunction of the transition functor attached to the identity simplex map, of the
transport of the sheaf along the identity equality of the simplicial diagram. -/
theorem pushforwardId_inr_inv_app (C : CocontinuousSimplicialSite.{u}) (n : SimplexCategory)
    (X : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) (Type u))
    (hX : (C.underlying.map (𝟙 n).op).toFunctor.op ⋙ X.obj = X.obj) :
    (pushforwardId (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).inv.app X =
      ⟨(((C.underlying.map (𝟙 n).op).toFunctor.op.ranAdjunction (Type u)).homEquiv X.obj X.obj)
        (eqToHom hX)⟩ := by
  have hco : (C.underlying.map (𝟙 n).op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (op n)))
      (topologyOfCoverings (C.coverage (op n))) := C.isCocontinuous (𝟙 n).op
  refine ((Iso.comp_hom_eq_id ((pushforwardId ⟨Sum.inr C⟩ n).app X)).mp ?_).symm
  dsimp only [pushforwardId, _root_.id, transitionMorphism, gStar, componentTopology, component]
  exact Sheaf.hom_ext <| cocontinuousPushforwardId_homEquiv_eqToHom
    (topologyOfCoverings (C.coverage (op n)))
    (w := (C.underlying.map (𝟙 n).op).toFunctor)
    (congrArg Cat.Hom.toFunctor (C.underlying.map_id (op n))) X hX

section

variable (C : CocontinuousSimplicialSite.{u})
  (G : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})))

/-- In case (B), the fibrewise functor from which the presheaf of a system is built: in
simplicial degree `c` it is the sections of the component sheaf of the system, read into the
opposite of `Type u` so that the functor out of the total category is a presheaf on it. -/
noncomputable abbrev systemFibreOpInr (c : SimplexCategoryᵒᵖ) :
    C.underlying.obj c ⥤ (Type u)ᵒᵖ :=
  ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c.unop).obj.rightOp

/-- In case (B), the transition of the presheaf of a system along a map of simplicial degrees:
the direct-image transition of the system, transposed along the Kan-extension adjunction of the
transition functor and read in the opposite target category. -/
noncomputable abbrev systemTransitionOpInr {c c' : SimplexCategoryᵒᵖ} (f : c ⟶ c') :
    systemFibreOpInr C G c ⟶ (C.underlying.map f).toFunctor ⋙ systemFibreOpInr C G c' :=
  NatTrans.rightOp
      ((((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G f.unop).hom))

/-- The unit law for the transitions of the presheaf of a system in case (B): the transition
attached to an identity map of simplicial degrees is the transport along the identity equality of
the simplicial diagram of categories. -/
theorem systemTransitionOpInr_id (c : SimplexCategoryᵒᵖ) :
    systemTransitionOpInr C G (𝟙 c) =
      eqToHom (Grothendieck.fib_map_id_eq (systemFibreOpInr C G) c) := by
  have hu : (C.underlying.map (𝟙 c.unop).op).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (C.underlying.map_id (op c.unop))
  have hX : (C.underlying.map (𝟙 c.unop).op).toFunctor.op ⋙
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c.unop).obj =
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c.unop).obj := by
    rw [hu]
    rfl
  have key : (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
        G (𝟙 c).unop).hom) =
      (((C.underlying.map (𝟙 c)).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _)
        (eqToHom hX) :=
    congrArg (fun t => t.hom)
      ((systemDirectTransition_id (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) G c.unop).trans
        (pushforwardId_inr_inv_app C c.unop _ hX))
  exact Eq.trans (congrArg NatTrans.rightOp ((Equiv.symm_apply_eq _).mpr key))
    (NatTrans.rightOp_eqToHom hX)

/-- The cocycle law for the transitions of the presheaf of a system in case (B): the transition
attached to a composite map of simplicial degrees is the composite of the two transitions,
transported along the composition equality of the simplicial diagram of categories. -/
theorem systemTransitionOpInr_comp {c₁ c₂ c₃ : SimplexCategoryᵒᵖ} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    systemTransitionOpInr C G (f ≫ g) = systemTransitionOpInr C G f ≫
      Functor.whiskerLeft (C.underlying.map f).toFunctor (systemTransitionOpInr C G g) ≫
        eqToHom (Grothendieck.fib_map_comp_eq (systemFibreOpInr C G) f g) := by
  have hu : (C.underlying.map f).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage c₁)) (topologyOfCoverings (C.coverage c₂)) :=
    C.isCocontinuous f
  have hv : (C.underlying.map g).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage c₂)) (topologyOfCoverings (C.coverage c₃)) :=
    C.isCocontinuous g
  have hw' : (C.underlying.map (f ≫ g)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage c₁)) (topologyOfCoverings (C.coverage c₃)) :=
    C.isCocontinuous (f ≫ g)
  have hcomp : ((C.underlying.map f).toFunctor ⋙ (C.underlying.map g).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage c₁)) (topologyOfCoverings (C.coverage c₃)) :=
    isCocontinuous_comp _ _ (topologyOfCoverings (C.coverage c₁))
      (topologyOfCoverings (C.coverage c₂))
  have hw : (C.underlying.map f).toFunctor ⋙ (C.underlying.map g).toFunctor =
      (C.underlying.map (f ≫ g)).toFunctor := by
    rw [C.underlying.map_comp]
    rfl
  have hE := cocontinuousTranspose_comp_ofEq
    (topologyOfCoverings (C.coverage c₁)) (topologyOfCoverings (C.coverage c₂))
    (topologyOfCoverings (C.coverage c₃))
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₁.unop)
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₂.unop).obj
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₃.unop).obj
    ((((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G f.unop).hom))
    ((((C.underlying.map g).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G g.unop).hom))
    hw rfl
  have ha : (((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₂.unop).obj
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₁.unop).obj)
      ((((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G f.unop).hom)) =
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G f.unop).hom) :=
    Equiv.apply_symm_apply _ _
  have hb : (((C.underlying.map g).toFunctor.op.ranAdjunction (Type u)).homEquiv
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₃.unop).obj
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₂.unop).obj)
      ((((C.underlying.map g).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G g.unop).hom)) =
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition G g.unop).hom) :=
    Equiv.apply_symm_apply _ _
  rw [ha, hb] at hE
  have key : (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
        G (f ≫ g).unop).hom) =
      (((C.underlying.map (f ≫ g)).toFunctor.op.ranAdjunction (Type u)).homEquiv
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₃.unop).obj
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₁.unop).obj)
        (eqToHom (congrArg (fun k : C.underlying.obj c₁ ⥤ C.underlying.obj c₃ =>
              k.op ⋙ ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₃.unop).obj)
            hw.symm) ≫
          Functor.whiskerLeft (C.underlying.map f).toFunctor.op
              ((((C.underlying.map g).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
                (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
                  G g.unop).hom)) ≫
            (((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
              (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
                G f.unop).hom)) :=
    (congrArg (fun t => t.hom) (systemDirectTransition_comp
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) G g.unop f.unop)).trans hE.symm
  have hRHS : systemTransitionOpInr C G f ≫
        Functor.whiskerLeft (C.underlying.map f).toFunctor (systemTransitionOpInr C G g) ≫
          eqToHom (Grothendieck.fib_map_comp_eq (systemFibreOpInr C G) f g) =
      NatTrans.rightOp
        (eqToHom (congrArg (fun k : C.underlying.obj c₁ ⥤ C.underlying.obj c₃ =>
              k.op ⋙ ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c₃.unop).obj)
            hw.symm) ≫
          Functor.whiskerLeft (C.underlying.map f).toFunctor.op
              ((((C.underlying.map g).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
                (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
                  G g.unop).hom)) ≫
            (((C.underlying.map f).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
              (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemDirectTransition
                G f.unop).hom)) := by
    rw [NatTrans.rightOp_comp, NatTrans.rightOp_comp, NatTrans.rightOp_whiskerLeft,
      NatTrans.rightOp_eqToHom, Category.assoc]
    rfl
  exact (congrArg NatTrans.rightOp ((Equiv.symm_apply_eq _).mpr key)).trans hRHS.symm


/-- **Stacks 09WF**, case (B). The presheaf on the total site underlying a system: in
simplicial degree `c` it is the sections of the component sheaf, and restriction along a
cross-fibre arrow is the transposed direct-image transition of the system. -/
noncomputable def systemPresheafInr :
    (Grothendieck C.underlying)ᵒᵖ ⥤ Type u :=
  (Grothendieck.functorFromOfEq (F := C.underlying) (E := (Type u)ᵒᵖ)
    (systemFibreOpInr C G) (fun {_ _} f => systemTransitionOpInr C G f)
    (systemTransitionOpInr_id C G)
    (fun _ _ _ f g => systemTransitionOpInr_comp C G f g)).leftOp

/-- In case (B), the restriction of the presheaf of a system to the component in a given
simplicial degree is the component sheaf of the system. -/
noncomputable def systemPresheafInrRestriction (c : SimplexCategoryᵒᵖ) :
    (Grothendieck.ι C.underlying c).op ⋙ systemPresheafInr C G ≅
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).systemSheaf G c.unop).obj :=
  (Functor.leftOpComp _ _).symm ≪≫
    (Functor.leftOpIso (Grothendieck.ιCompFunctorFromOfEq (systemFibreOpInr C G)
      (fun {_ _} f => systemTransitionOpInr C G f) (systemTransitionOpInr_id C G)
      (fun _ _ _ f g => systemTransitionOpInr_comp C G f g) c)).symm ≪≫
    Functor.rightOpLeftOpIso _

/-- In case (A), the restriction of the presheaf of a system to the component in a given
simplicial degree is the component sheaf of the system. -/
noncomputable def systemPresheafInlRestriction (D : SimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u})))
    (R : SimplexCategoryᵒᵖ) :
    (Pseudofunctor.CoGrothendieck.ι D.totalPseudofunctor R).op ⋙ systemPresheafInl D H ≅
      ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemSheaf H R.unop).obj :=
  (Functor.leftOpComp _ _).symm ≪≫
    (Functor.leftOpIso (Pseudofunctor.CoGrothendieck.ιCompFunctorFrom
      (F := D.totalPseudofunctor) (E := (Type u)ᵒᵖ)
      (fun R => (((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemSheaf H R.unop).obj).rightOp)
      (fun {_ _} f => NatTrans.rightOp
        (((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H f.unop).hom))
      (systemDirectTransition_rightOp_id D H)
      (fun {_ _ _} f g => systemDirectTransition_rightOp_comp D H f g) R)).symm ≪≫
    Functor.rightOpLeftOpIso _

/-- **Stacks 09WF**, case (A). The presheaf underlying a system is a sheaf on the total site:
the total coverage is generated by the fibrewise covering families, and the restriction of the
presheaf to each fibre is the component sheaf of the system. -/
theorem systemPresheafInl_isSheaf (D : SimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}))) :
    Presieve.IsSheaf (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).totalTopology
      (systemPresheafInl D H) := by
  have h1 : D.totalCoverage.HasPullbacks := D.totalCoverage_hasPullbacks
  have h2 : D.totalCoverage.IsStableUnderBaseChange := D.totalCoverage_isStableUnderBaseChange
  refine (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange
    (J := D.totalCoverage) (systemPresheafInl D H)).mpr ?_
  intro X R hR
  obtain ⟨T, hT, rfl⟩ := hR
  refine Presieve.isSheafFor_map _ _ _ ?_
  exact isSheafFor_of_iso_sheaf _ (systemPresheafInlRestriction D H X.base) _
    (Precoverage.generate_mem_toGrothendieck hT)

/-- **Stacks 09WF**, case (B). The presheaf underlying a system is a sheaf on the total site:
the total coverage is generated by the fibrewise covering families, and the restriction of the
presheaf to each fibre is the component sheaf of the system. -/
theorem systemPresheafInr_isSheaf :
    Presieve.IsSheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (systemPresheafInr C G) := by
  refine isSheaf_topologyOfCoverings
    (SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite C.isCocontinuous
      C.hasCoverPullbacks) _ ?_
  intro X E hE
  obtain ⟨E', hE', rfl⟩ : ∃ E'' : PreZeroHypercover.{u} X.fiber,
      C.coverage X.base ⟨X.fiber, E''⟩ ∧
        E = E''.map (Grothendieck.ι C.underlying X.base) := hE
  refine Presieve.isSheafFor_presieve₀_map (Grothendieck.ι C.underlying X.base) _ E' ?_
  exact isSheafFor_of_iso_sheaf _ (systemPresheafInrRestriction C G X.base) _
    (Precoverage.generate_mem_toGrothendieck ⟨E', hE', rfl⟩)

end


/-- **Stacks 09WF.** The presheaf on the total site underlying a system, in both cases of the
situation. -/
noncomputable def systemPresheaf (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) : (S.totalCategory)ᵒᵖ ⥤ Type u := by
  rcases S with ⟨D | D⟩
  · exact systemPresheafInl D G
  · exact systemPresheafInr D G

/-- **Stacks 09WF.** The presheaf on the total site underlying a system is a sheaf. -/
theorem systemPresheaf_isSheaf (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) :
    Presieve.IsSheaf S.totalTopology (S.systemPresheaf G) := by
  rcases S with ⟨D | D⟩
  · exact systemPresheafInl_isSheaf D G
  · exact systemPresheafInr_isSheaf D G

/-- **Stacks 09WF.** The sheaf on the total site underlying a system. -/
noncomputable def systemTotalSheaf (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) : Sheaf S.totalTopology (Type u) :=
  ⟨S.systemPresheaf G, (isSheaf_iff_isSheaf_of_type _ _).mpr (S.systemPresheaf_isSheaf G)⟩

/-- The restriction of the presheaf of a system to the component in a given simplicial degree
is the component sheaf of the system. -/
noncomputable def systemPresheafRestriction (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) (n : SimplexCategory) :
    (S.inclusion n).op ⋙ S.systemPresheaf G ≅ (S.systemSheaf G n).obj := by
  rcases S with ⟨D | D⟩
  · exact systemPresheafInlRestriction D G (op n)
  · exact systemPresheafInrRestriction D G (op n)


/-- **Stacks 09WF.** The restriction of the total-site sheaf of a system to the component in a
given simplicial degree is the component sheaf of the system. -/
noncomputable def restrictIso (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) (n : SimplexCategory) :
    (S.restrict n).obj (S.systemTotalSheaf G) ≅ S.systemSheaf G n where
  hom := ⟨(S.systemPresheafRestriction G n).hom⟩
  inv := ⟨(S.systemPresheafRestriction G n).inv⟩
  hom_inv_id := Sheaf.hom_ext (S.systemPresheafRestriction G n).hom_inv_id
  inv_hom_id := Sheaf.hom_ext (S.systemPresheafRestriction G n).inv_hom_id

/-- In case (A), restriction of the presheaf of a system along a cross-fibre arrow with
identity fibre component is the direct-image transition of the system, on sections. -/
theorem systemPresheafInl_map_continuousInclusionTransition (D : SimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u})))
    {m n : SimplexCategory} (φ : m ⟶ n) (W : D.underlying.obj m) :
    (systemPresheafInl D H).map ((continuousInclusionTransition D φ).app W).op =
      (((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H φ).hom.app
        (op W)) := by
  have h := Pseudofunctor.CoGrothendieck.functorFrom_map_ιNatTrans_app
    (F := D.totalPseudofunctor) (E := (Type u)ᵒᵖ)
    (fun R => (((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemSheaf H R.unop).obj).rightOp)
    (fun {_ _} f => NatTrans.rightOp
      (((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H f.unop).hom))
    (systemDirectTransition_rightOp_id D H)
    (fun {_ _ _} f g => systemDirectTransition_rightOp_comp D H f g) φ.op W
  exact congrArg Quiver.Hom.unop h


/-- **Stacks 09WF**, case (A). The fibrewise identifications of the total-site sheaf of a
system carry the direct-image transitions of its restrictions to the direct-image transitions of
the system. -/
theorem restrictIso_systemDirectTransition_inl (D : SimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u})))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictIso (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) H m).hom ≫
        (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H φ =
      (restrictTransition (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) φ).app
          ((⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}).systemTotalSheaf H) ≫
        (transitionMorphism (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) φ).pushforward.map
          (restrictIso (⟨Sum.inl D⟩ : SimplicialSiteSituation.{u}) H n).hom :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun V =>
    (systemPresheafInl_map_continuousInclusionTransition D H φ V.unop).symm


/-- In case (B), restriction of the presheaf of a system along a cross-fibre arrow with
identity fibre component is the transposed direct-image transition of the system, on sections. -/
theorem systemPresheafInr_map_ιNatTrans (D : CocontinuousSimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u})))
    {m n : SimplexCategory} (φ : m ⟶ n) (U : D.underlying.obj (op n)) :
    (systemPresheafInr D H).map ((Grothendieck.ιNatTrans (F := D.underlying) φ.op).app U).op =
      ((((D.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H φ).hom)).app
        (op U) := by
  have h := Grothendieck.functorFromOfEq_map_ιNatTrans_app
    (systemFibreOpInr D H) (fun {_ _} f => systemTransitionOpInr D H f)
    (systemTransitionOpInr_id D H)
    (fun _ _ _ f g => systemTransitionOpInr_comp D H f g) φ.op U
  exact congrArg Quiver.Hom.unop h

/-- **Stacks 09WF**, case (B). The fibrewise identifications of the total-site sheaf of a
system carry the direct-image transitions of its restrictions to the direct-image transitions of
the system. -/
theorem restrictIso_systemDirectTransition_inr (D : CocontinuousSimplicialSite.{u})
    (H : SimplicialSheafSystem
      (componentPseudofunctor (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u})))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictIso (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) H m).hom ≫
        (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemDirectTransition H φ =
      (restrictTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app
          ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemTotalSheaf H) ≫
        (transitionMorphism (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).pushforward.map
          (restrictIso (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) H n).hom := by
  apply Sheaf.hom_ext
  refine ((((D.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv
    (((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).restrict m).obj
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemTotalSheaf H)).obj
    ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemSheaf H n).obj).symm).injective ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _).symm
  exact NatTrans.ext <| funext fun U => (systemPresheafInr_map_ιNatTrans D H φ U.unop).symm.trans
    (restrictTransition_inr_app D φ
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).systemTotalSheaf H) U.unop).symm


/-- **Stacks 09WF.** The fibrewise identifications of the total-site sheaf of a system carry
the direct-image transitions of its restrictions to the direct-image transitions of the
system. -/
theorem restrictIso_systemDirectTransition (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.restrictIso G m).hom ≫ S.systemDirectTransition G φ =
      (S.restrictTransition φ).app (S.systemTotalSheaf G) ≫
        (S.transitionMorphism φ).pushforward.map (S.restrictIso G n).hom := by
  rcases S with ⟨D | D⟩
  · exact restrictIso_systemDirectTransition_inl D G φ
  · exact restrictIso_systemDirectTransition_inr D G φ

/-- **Stacks 09WF.** The inverse-image form of
`CategoryTheory.SimplicialSiteSituation.restrictIso_systemDirectTransition`, obtained from it by
the topos adjunction of the transition morphism. This is the one law of the isomorphism of
systems below. -/
theorem restrictIso_systemFibreTransition (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map (S.restrictIso G m).hom ≫
        S.systemFibreTransition G φ =
      (S.fiberTransition φ).app (S.systemTotalSheaf G) ≫ (S.restrictIso G n).hom := by
  refine ((S.transitionMorphism φ).adj.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    fiberTransition_adj]
  exact S.restrictIso_systemDirectTransition G φ


/-- **Stacks 09WF.** The system of restrictions of the total-site sheaf of a system is that
system: the components are the fibrewise identifications and the one law is
`CategoryTheory.SimplicialSiteSituation.restrictIso_systemFibreTransition`. -/
noncomputable def restrictSystemTotalSheafIso (S : SimplicialSiteSituation.{u})
    (G : SimplicialSheafSystem (componentPseudofunctor S)) :
    restrictSystem S (S.systemTotalSheaf G) ≅ G :=
  Lax.LaxTrans.isoMk
    (fun a => Cat.Hom.isoMk
      (Discrete.natIso (fun _ => AsSmall.up.mapIso (S.restrictIso G a.as))))
    (fun {a b} f => by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext x
      change AsSmall.up.{u, u + 1, u + 1}.map
            ((S.transitionMorphism f.as).inverseImage.map (S.restrictIso G a.as).hom) ≫
          AsSmall.up.{u, u + 1, u + 1}.map (S.systemFibreTransition G f.as) =
        AsSmall.up.{u, u + 1, u + 1}.map
            ((S.fiberTransition f.as).app (S.systemTotalSheaf G)) ≫
          AsSmall.up.{u, u + 1, u + 1}.map (S.restrictIso G b.as).hom
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun t => AsSmall.up.{u, u + 1, u + 1}.map t)
        (S.restrictIso_systemFibreTransition G f.as))

/-- **Stacks 09WF.** The functor taking a sheaf on the total site to its system of
restrictions is essentially surjective: every system is the system of restrictions of the sheaf
built from it. This is the descent construction. -/
instance restrictSystemFunctor_essSurj (S : SimplicialSiteSituation.{u}) :
    (restrictSystemFunctor S).EssSurj where
  mem_essImage G := ⟨S.systemTotalSheaf G, ⟨S.restrictSystemTotalSheafIso G⟩⟩


/-- **Stacks 09WF.** The presentation of the sheaves on the total site as systems on the
component topoi, with no hypotheses: the system of restrictions is an equivalence. The
equivalence `Sh(C_total) ≌ SimplicialSheafSystem (componentPseudofunctor S)` of the tag is its
`totalEquivalence` field. -/
@[stacks 09WF "equivalence of categories"]
noncomputable def totalPresentation (S : SimplicialSiteSituation.{u}) :
    SimplicialSheafPresentation S :=
  restrictPresentation S

/-- **Stacks 09WF.** The transition of the system attached to a sheaf on the total site is the
inverse-image transition of its restrictions: under the identification of the components of the
system with those restrictions, `transition` is `fiberTransition`. -/
@[stacks 09WF "transition by restriction"]
theorem totalPresentation_transition_restriction (S : SimplicialSiteSituation.{u})
    (F : Sheaf S.totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (totalPresentation S).transition F φ ≫
        ((totalPresentation S).componentRestrictionIso F n).hom =
      (S.transitionMorphism φ).inverseImage.map
          ((totalPresentation S).componentRestrictionIso F m).hom ≫
        (S.fiberTransition φ).app F := by
  show (𝟙 _ ≫ (S.fiberTransition φ).app F) ≫ 𝟙 ((S.restrict n).obj F) =
    (S.transitionMorphism φ).inverseImage.map (𝟙 ((S.restrict m).obj F)) ≫
      (S.fiberTransition φ).app F
  rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]

end SimplicialSiteSituation

end CategoryTheory
end
