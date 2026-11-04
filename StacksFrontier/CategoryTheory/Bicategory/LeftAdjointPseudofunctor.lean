module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The pseudofunctor of left adjoints of a system of pushforwards

Let `C` be a category and suppose given, for every object `X` of `C`, a category `obj X`, and
for every morphism `f : X ⟶ Y` an adjunction `L f ⊣ R f` with `R f : obj X ⥤ obj Y` and
`L f : obj Y ⥤ obj X`. Suppose the covariant family `R` carries comparison isomorphisms
`R (𝟙 X) ≅ 𝟭` and `R (f ≫ g) ≅ R f ⋙ R g` satisfying the three coherences of a pseudofunctor.
Then the contravariant family `L` of left adjoints is a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, with the given categories as its fibres and the given left
adjoint as its `map`, both on the nose.

This is the situation of a system of morphisms of topoi: the direct images compose covariantly
and strictly enough to be handled by hand, while the inverse images are left adjoints, for
which no composition isomorphism is available except as the adjoint mate of the one for the
direct images.

The proof is the mate argument. `CategoryTheory.conjugateEquiv` is a bijection between
`2`-cells of left adjoints and `2`-cells of their right adjoints, and Mathlib's
`CategoryTheory.conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft`,
`conjugateEquiv_whiskerRight` and `conjugateEquiv_associator_hom` say that it turns a pasting
of `2`-cells into the mate of the reversed pasting. Each of the three coherences for `L` is
therefore the image under that bijection of the corresponding coherence for `R`, and
injectivity of a bijection finishes it. Since the data here lie on the right adjoints and the
coherences to be proved on the left adjoints, the `symm` direction of each transfer lemma is
what is needed, and those are proved below from Mathlib's forward versions.

## Main definitions

* `CategoryTheory.LocallyDiscrete.lId` and `CategoryTheory.LocallyDiscrete.lComp`: the mates of
  the identity and composition comparisons, on the left adjoints;
* `CategoryTheory.LocallyDiscrete.mkPseudofunctorOfLeftAdjoints`: the pseudofunctor.

## Main results

* `CategoryTheory.LocallyDiscrete.lComp_assoc`: the associativity coherence (the pentagon) for
  the mates, and `CategoryTheory.LocallyDiscrete.lComp_comp_id`,
  `CategoryTheory.LocallyDiscrete.lComp_id_comp`: its two unitor coherences;
* `CategoryTheory.conjugateEquiv_symm_whiskerLeft`,
  `CategoryTheory.conjugateEquiv_symm_whiskerRight`,
  `CategoryTheory.conjugateEquiv_symm_associator_hom`,
  `CategoryTheory.conjugateEquiv_symm_rightUnitor_inv` and
  `CategoryTheory.conjugateEquiv_symm_leftUnitor_inv`: the `symm` halves of Mathlib's mate
  transfer lemmas;
* `CategoryTheory.leftAdjointUniq_ofNatIsoRight_eq`: a comparison of left adjoints built with
  `CategoryTheory.Adjunction.leftAdjointUniq` out of an isomorphism of right adjoints **is**
  the adjoint mate of that isomorphism, with
  `CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight` the equation it comes from.
  This is what identifies a composition isomorphism built the `leftAdjointUniq` way — which is
  how Stacks 03G2 part (3) builds the inverse-image one — with `lComp` above.

## Implementation notes

This is the dual of `CategoryTheory.Over.pullbackPseudofunctor`
(`StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor`), and it does not subsume
it: there the coherent family is the family of *left* adjoints `Over.map` and the derived one
is the family of right adjoints `Over.pullback`, so the transfer runs in the opposite
direction and uses Mathlib's forward lemmas together with that file's
`conjugateEquiv_leftUnitor_inv` and `conjugateEquiv_rightUnitor_inv`. The two files are
transposes of one another; neither statement implies the other.

The three coherence hypotheses are stated exactly as they come out of the mate transfer, which
is also the shape in which Mathlib states them for its own example: compare
`CategoryTheory.GrothendieckTopology.overMapPullback_assoc`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Mates

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

/-- The `symm` half of `CategoryTheory.conjugateEquiv_whiskerLeft`. -/
lemma conjugateEquiv_symm_whiskerLeft
    {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : R₁ ⟶ R₂) :
    (conjugateEquiv (adj.comp adj₁) (adj.comp adj₂)).symm (Functor.whiskerRight τ R) =
      Functor.whiskerLeft L ((conjugateEquiv adj₁ adj₂).symm τ) := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]

/-- The `symm` half of `CategoryTheory.conjugateEquiv_whiskerRight`. -/
lemma conjugateEquiv_symm_whiskerRight
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : R₁ ⟶ R₂) :
    (conjugateEquiv (adj₁.comp adj) (adj₂.comp adj)).symm (Functor.whiskerLeft R τ) =
      Functor.whiskerRight ((conjugateEquiv adj₁ adj₂).symm τ) L := by
  rw [Equiv.symm_apply_eq, conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]

/-- The `symm` half of `CategoryTheory.conjugateEquiv_associator_hom`. -/
lemma conjugateEquiv_symm_associator_hom
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    (conjugateEquiv (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)).symm
        (Functor.associator _ _ _).hom = (Functor.associator _ _ _).hom :=
  (Equiv.symm_apply_eq _).2 (conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃).symm

/-- The `symm` half of `CategoryTheory.conjugateEquiv_leftUnitor_hom`: the mate of the inverse
right unitor of a right adjoint is the left unitor of its left adjoint. -/
lemma conjugateEquiv_symm_rightUnitor_inv
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    (conjugateEquiv adj (Adjunction.id.comp adj)).symm (Functor.rightUnitor R).inv =
      (Functor.leftUnitor L).hom :=
  (Equiv.symm_apply_eq _).2 (conjugateEquiv_leftUnitor_hom adj).symm

/-- The `symm` half of `CategoryTheory.conjugateEquiv_rightUnitor_hom`: the mate of the inverse
left unitor of a right adjoint is the right unitor of its left adjoint. -/
lemma conjugateEquiv_symm_leftUnitor_inv
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    (conjugateEquiv adj (adj.comp Adjunction.id)).symm (Functor.leftUnitor R).inv =
      (Functor.rightUnitor L).hom :=
  (Equiv.symm_apply_eq _).2 (conjugateEquiv_rightUnitor_hom adj).symm

/-- The unit of an adjunction transported along an isomorphism of right adjoints. -/
lemma ofNatIsoRight_unit {L : A ⥤ B} {R R' : B ⥤ A} (adj : L ⊣ R) (e : R ≅ R') :
    (adj.ofNatIsoRight e).unit = adj.unit ≫ Functor.whiskerLeft L e.hom :=
  rfl

/-- The adjoint mate of the identification of two left adjoints of isomorphic right adjoints
is that isomorphism. -/
lemma conjugateEquiv_leftAdjointUniq_ofNatIsoRight
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv adj₁ adj₂ (adj₂.leftAdjointUniq (adj₁.ofNatIsoRight e)).hom = e.hom := by
  ext X
  rw [conjugateEquiv_apply_app, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app adj₂ (adj₁.ofNatIsoRight e) (R₁.obj X),
    ofNatIsoRight_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  have hn : e.hom.app (L₁.obj (R₁.obj X)) ≫ R₂.map (adj₁.counit.app X) =
      R₁.map (adj₁.counit.app X) ≫ e.hom.app X := (e.hom.naturality _).symm
  rw [hn, ← Category.assoc, adj₁.right_triangle_components, Category.id_comp]

/-- Consequently a composition isomorphism of left adjoints built with
`CategoryTheory.Adjunction.leftAdjointUniq` out of an isomorphism of right adjoints is the
`CategoryTheory.conjugateEquiv` preimage of that isomorphism, i.e. its adjoint mate. -/
lemma leftAdjointUniq_ofNatIsoRight_eq
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    (adj₂.leftAdjointUniq (adj₁.ofNatIsoRight e)).hom =
      (conjugateEquiv adj₁ adj₂).symm e.hom :=
  (Equiv.eq_symm_apply _).2 (conjugateEquiv_leftAdjointUniq_ofNatIsoRight adj₁ adj₂ e)

end Mates

namespace LocallyDiscrete

universe v u v' u'

variable {C : Type u} [Category.{v} C]
  (obj : C → Cat.{v', u'})
  (L : ∀ {X Y : C}, (X ⟶ Y) → (obj Y ⥤ obj X))
  (R : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⥤ obj Y))
  (adj : ∀ {X Y : C} (f : X ⟶ Y), L f ⊣ R f)
  (rId : ∀ X : C, R (𝟙 X) ≅ 𝟭 _)
  (rComp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), R (f ≫ g) ≅ R f ⋙ R g)

/-- The mate of the identity comparison, on the left adjoints. -/
noncomputable def lId (X : C) : L (𝟙 X) ≅ 𝟭 (obj X) :=
  ((conjugateIsoEquiv (adj (𝟙 X)) Adjunction.id).symm (rId X)).symm

/-- The mate of the composition comparison, on the left adjoints. -/
noncomputable def lComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    L (f ≫ g) ≅ L g ⋙ L f :=
  ((conjugateIsoEquiv (adj (f ≫ g)) ((adj g).comp (adj f))).symm (rComp f g)).symm

/-- The hom of `lId` is the conjugate preimage of the inverse of `rId X`. -/
lemma lId_hom (X : C) :
    (lId obj L R adj rId X).hom =
      (conjugateEquiv Adjunction.id (adj (𝟙 X))).symm (rId X).inv := rfl

/-- The hom of `lComp f g` is the conjugate preimage of the inverse of `rComp f g`. -/
lemma lComp_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lComp obj L R adj rComp f g).hom =
      (conjugateEquiv ((adj g).comp (adj f)) (adj (f ≫ g))).symm (rComp f g).inv := rfl

/-- The inverse of `lComp f g` is the conjugate preimage of the hom of `rComp f g`. -/
lemma lComp_inv {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lComp obj L R adj rComp f g).inv =
      (conjugateEquiv (adj (f ≫ g)) ((adj g).comp (adj f))).symm (rComp f g).hom := rfl

/-- The mate of the identification of the right adjoints of two equal morphisms is the
identification of their left adjoints. -/
private lemma conjugateEquiv_symm_eqToHom {X Y : C} {u v : X ⟶ Y} (e : u = v) :
    (conjugateEquiv (adj u) (adj v)).symm (eqToHom (congrArg (fun k : X ⟶ Y => R k) e)) =
      eqToHom (congrArg (fun k : X ⟶ Y => L k) e.symm) := by
  subst e
  simp [conjugateEquiv_symm_id (adj u)]

section Coherences

variable
  (hassoc : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
    (rComp (f ≫ g) h).hom ≫ Functor.whiskerRight (rComp f g).hom (R h) ≫
        (Functor.associator (R f) (R g) (R h)).hom ≫
          Functor.whiskerLeft (R f) (rComp g h).inv ≫ (rComp f (g ≫ h)).inv =
      eqToHom (congrArg (fun k : X ⟶ W => R k) (Category.assoc f g h)))
  (hcompId : ∀ {X Y : C} (p : X ⟶ Y),
    (Functor.rightUnitor (R p)).inv ≫ Functor.whiskerLeft (R p) (rId Y).inv ≫
        (rComp p (𝟙 Y)).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => R k) (Category.comp_id p).symm))
  (hidComp : ∀ {X Y : C} (p : X ⟶ Y),
    (Functor.leftUnitor (R p)).inv ≫ Functor.whiskerRight (rId X).inv (R p) ≫
        (rComp (𝟙 X) p).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => R k) (Category.id_comp p).symm))

include hassoc in
/-- The associativity coherence (the pentagon) for the mates. -/
lemma lComp_assoc {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (lComp obj L R adj rComp f (g ≫ h)).hom ≫
      Functor.whiskerRight (lComp obj L R adj rComp g h).hom (L f) ≫
        (Functor.associator (L h) (L g) (L f)).hom ≫
          Functor.whiskerLeft (L h) (lComp obj L R adj rComp f g).inv ≫
            (lComp obj L R adj rComp (f ≫ g) h).inv =
      eqToHom (congrArg (fun k : X ⟶ W => L k) (Category.assoc f g h).symm) := by
  rw [lComp_hom, lComp_hom, lComp_inv, lComp_inv,
    ← conjugateEquiv_symm_whiskerRight ((adj h).comp (adj g)) (adj (g ≫ h)) (adj f),
    ← conjugateEquiv_symm_associator_hom (adj h) (adj g) (adj f),
    ← conjugateEquiv_symm_whiskerLeft (adj (f ≫ g)) ((adj g).comp (adj f)) (adj h)]
  simp only [conjugateEquiv_symm_comp, Category.assoc]
  rw [hassoc f g h]
  exact conjugateEquiv_symm_eqToHom obj L R adj (Category.assoc f g h)

include hcompId in
/-- The left unitor coherence for the mates. -/
lemma lComp_comp_id {X Y : C} (p : X ⟶ Y) :
    (lComp obj L R adj rComp p (𝟙 Y)).hom ≫
      Functor.whiskerRight (lId obj L R adj rId Y).hom (L p) ≫
        (Functor.leftUnitor (L p)).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => L k) (Category.comp_id p)) := by
  rw [lComp_hom, lId_hom,
    ← conjugateEquiv_symm_whiskerRight Adjunction.id (adj (𝟙 Y)) (adj p),
    ← conjugateEquiv_symm_rightUnitor_inv (adj p)]
  simp only [conjugateEquiv_symm_comp, Category.assoc]
  rw [hcompId p]
  exact conjugateEquiv_symm_eqToHom obj L R adj (Category.comp_id p).symm

include hidComp in
/-- The right unitor coherence for the mates. -/
lemma lComp_id_comp {X Y : C} (p : X ⟶ Y) :
    (lComp obj L R adj rComp (𝟙 X) p).hom ≫
      Functor.whiskerLeft (L p) (lId obj L R adj rId X).hom ≫
        (Functor.rightUnitor (L p)).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => L k) (Category.id_comp p)) := by
  rw [lComp_hom, lId_hom,
    ← conjugateEquiv_symm_whiskerLeft Adjunction.id (adj (𝟙 X)) (adj p),
    ← conjugateEquiv_symm_leftUnitor_inv (adj p)]
  simp only [conjugateEquiv_symm_comp, Category.assoc]
  rw [hidComp p]
  exact conjugateEquiv_symm_eqToHom obj L R adj (Category.id_comp p).symm

include hassoc hcompId hidComp in
/-- **The pseudofunctor of left adjoints.** Given, for each object `X` of a category `C`, a
category `obj X`, and for each `f : X ⟶ Y` an adjunction `L f ⊣ R f` with
`R f : obj X ⥤ obj Y`, together with comparison isomorphisms `rId` and `rComp` on the `R` side
satisfying the three pseudofunctor coherences, the left adjoints assemble into a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose fibres are the given categories and whose `map` is the given
left adjoint, both on the nose. -/
noncomputable def mkPseudofunctorOfLeftAdjoints :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ obj X.unop)
    (fun {_ _} φ ↦ Cat.Hom.ofFunctor (L φ.unop))
    (fun X ↦ Cat.Hom.isoMk (lId obj L R adj rId X.unop))
    (fun {_ _ _} φ ψ ↦ Cat.Hom.isoMk (lComp obj L R adj rComp ψ.unop φ.unop))
    (fun {_ _ _ _} φ ψ χ ↦ by
      ext1
      simpa using lComp_assoc obj L R adj rComp hassoc χ.unop ψ.unop φ.unop)
    (fun {_ _} φ ↦ by
      ext1
      simpa using lComp_comp_id obj L R adj rId rComp hcompId φ.unop)
    (fun {_ _} φ ↦ by
      ext1
      simpa using lComp_id_comp obj L R adj rId rComp hidComp φ.unop)

include hassoc hcompId hidComp in
/-- The pseudofunctor of left adjoints sends `X` to the category `obj X.unop`. -/
@[simp]
lemma mkPseudofunctorOfLeftAdjoints_obj (X : Cᵒᵖ) :
    (mkPseudofunctorOfLeftAdjoints obj L R adj rId rComp hassoc hcompId hidComp).obj
      (.mk X) = obj X.unop := rfl

include hassoc hcompId hidComp in
/-- The pseudofunctor of left adjoints sends `f.op` to the left adjoint `L f`. -/
@[simp]
lemma mkPseudofunctorOfLeftAdjoints_map {X Y : C} (f : X ⟶ Y) :
    (mkPseudofunctorOfLeftAdjoints obj L R adj rId rComp hassoc hcompId hidComp).map
      f.op.toLoc = Cat.Hom.ofFunctor (L f) := rfl

end Coherences

end LocallyDiscrete

end CategoryTheory

end
