module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward

/-!
# The two squares of Stacks 04H1 are Beck–Chevalley mates of one another

Let `f : E ⟶ D` be a morphism of topoi, let `G` be an object of `D` and put `F = f⁻¹G`.  Stacks
04H1 records the commutativity of the localization square
```
      E/F --f'--> D/G
    j_F ↓          ↓ j_G
       E --f-->    D
```
twice: on inverse images, as `MorphismOfTopoi.inverseImageCompToOverIso`, and on the pushforwards,
as `MorphismOfTopoi.toOverCompPushforwardIso`.  This file proves that the second is the
Beck–Chevalley *mate* of the first, across the two vertical adjunctions `f⁻¹ ⊣ f_*` and
`(f')⁻¹ ⊣ (f')_*`.  That identity is what lets a structure map be transported across the square:
it is the statement that reading an inverse-image comparison through the adjunctions produces the
pushforward comparison, and nothing weaker determines the two isomorphisms against each other.

## Main results

* `Stacks.CategoryTheory.mateEquiv_eq_of_homEquiv_symm`: a 2-cell is *the* mate of another as
  soon as its adjunct is the one `CategoryTheory.mateEquiv_counit` prescribes; this is the
  determination criterion used to identify a mate that was built by other means, in the form of
  the counit equation of `Stacks.CategoryTheory.mateEquiv_eq_of_counit`.
* `Stacks.CategoryTheory.homEquiv_symm_mateEquiv`: the element-level mates correspondence.  The
  adjunct of a morphism pushed along the top of the square and composed with the mate is the
  2-cell followed by the adjunct of the morphism itself.
* `Stacks.CategoryTheory.homEquiv_symm_mateEquiv_of_eq`: the same with the mate supplied by an
  equation, which is how it is applied to an isomorphism built by other means.
* `Stacks.CategoryTheory.mateEquiv_transport`: mates are preserved by transporting the right-hand
  adjunction of the square along two equivalences and the two vertical functors along the
  corresponding comparison isomorphisms.
* `Stacks.CategoryTheory.map_comp_four`: an auxiliary contraction of a four-fold composite under a
  functor, used where two of the four factors become identities.
* `Stacks.CategoryTheory.homEquiv_symm_comp_apply` and
  `Stacks.CategoryTheory.rightAdjointUniq_eqRec_hom`: the two pieces of adjunction calculus the
  proofs need — the adjunct under a composite of adjunctions, and the comparison of right adjoints
  attached to an *equality* of left adjoints.
* `MorphismOfTopoi.mateEquiv_eqToHom_post_forget`: Stacks 04H1's inverse-image square is the mate,
  across the two localization adjunctions `j_! ⊣ j⁻¹`, of the identity
  `(f')⁻¹ ⋙ j_{F!} = j_{G!} ⋙ f⁻¹`.
* `MorphismOfTopoi.mateEquiv_inverseImageCompToOverIso_inv`: **Stacks 04H1's pushforward square is
  the mate of its inverse-image square.**

## Implementation notes

The proof of the main result is Mathlib's `CategoryTheory.iterated_mateEquiv_conjugateEquiv`: all
four functors of the square have left adjoints, so taking mates twice — once across the horizontal
adjunctions `Over.forget ⊣ toOver`, once across the vertical adjunctions `f⁻¹ ⊣ f_*` — is the same
as taking the conjugate of the original 2-cell.  The original 2-cell here is the strict identity
`Over.post_forget_eq_forget_comp`, and the conjugate of that identity is exactly the comparison of
right adjoints that `MorphismOfTopoi.toOverCompPushforwardIso` is defined to be; that last
identification is `Stacks.CategoryTheory.rightAdjointUniq_eqRec_hom`, which says that transporting
an adjunction along an *equality* of left adjoints turns `Adjunction.rightAdjointUniq` into the
conjugate of the corresponding `eqToHom`.

Only the first of the two mate steps needs a computation, and it is the one-line one: the mate of
the strict identity is pinned by its counit equation, which on underlying objects says
`μ⁻¹ ≫ fst = f⁻¹(fst)`, i.e. that the comparison of `f⁻¹` with binary products is compatible with
the first projection (`CategoryTheory.Functor.Monoidal.μ_fst`).

The 2-cells here are the *inverse* directions of the two isomorphisms of Stacks 04H1, since the
mates correspondence is a bijection on 2-cells and those are the directions that compose.

## References

* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section Determination

variable {A : Type u₁} {B : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E] [Category.{v₄} F]
variable {Gf : A ⥤ E} {H : B ⥤ F} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- **A 2-cell is the mate of another as soon as it satisfies the adjunct equation.**  The mate of
`α` is the unique 2-cell whose adjunct at every object is `α` followed by the counit, because the
adjunct is a bijection; so an isomorphism built by other means is *the* mate once that equation is
checked for it. -/
theorem mateEquiv_eq_of_homEquiv_symm (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare Gf L₁ L₂ H) (β : TwoSquare R₁ H Gf R₂)
    (h : ∀ d : B, (adj₂.homEquiv (Gf.obj (R₁.obj d)) (H.obj d)).symm (β.natTrans.app d) =
      α.natTrans.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) :
    mateEquiv adj₁ adj₂ α = β := by
  refine mateEquiv_eq_of_counit adj₁ adj₂ α β fun d => ?_
  exact (Adjunction.homEquiv_counit ..).symm.trans (h d)

/-- **The element-level mates correspondence.**  For a morphism `φ : W ⟶ R₁ Z`, the adjunct of
`Gf φ` followed by the mate of `α` is `α` followed by the image under `H` of the adjunct of `φ`.

This is `CategoryTheory.mateEquiv_counit` with a morphism prepended; it is the form in which a
structure map, which is an adjunct, is carried across a Beck–Chevalley square. -/
theorem homEquiv_symm_mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare Gf L₁ L₂ H) {W : A} {Z : B} (φ : W ⟶ R₁.obj Z) :
    (adj₂.homEquiv (Gf.obj W) (H.obj Z)).symm
        (Gf.map φ ≫ (mateEquiv adj₁ adj₂ α).natTrans.app Z) =
      α.natTrans.app W ≫ H.map ((adj₁.homEquiv W Z).symm φ) := by
  have hn : L₂.map (Gf.map φ) ≫ α.natTrans.app (R₁.obj Z) =
      α.natTrans.app W ≫ H.map (L₁.map φ) := α.natTrans.naturality φ
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    mateEquiv_counit adj₁ adj₂ α Z, ← Category.assoc, hn, Category.assoc,
    Adjunction.homEquiv_counit, Functor.map_comp]

/-- `Stacks.CategoryTheory.homEquiv_symm_mateEquiv` with the mate given by an equation, so that
the conclusion is stated in terms of an isomorphism constructed by other means rather than in
terms of `CategoryTheory.mateEquiv`. -/
theorem homEquiv_symm_mateEquiv_of_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare Gf L₁ L₂ H) (β : TwoSquare R₁ H Gf R₂) (hm : mateEquiv adj₁ adj₂ α = β)
    {W : A} {Z : B} (φ : W ⟶ R₁.obj Z) :
    (adj₂.homEquiv (Gf.obj W) (H.obj Z)).symm (Gf.map φ ≫ β.natTrans.app Z) =
      α.natTrans.app W ≫ H.map ((adj₁.homEquiv W Z).symm φ) := by
  subst hm
  exact homEquiv_symm_mateEquiv adj₁ adj₂ α φ

end Determination

section Calculus

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- The inverse hom-set bijection of a composite of adjunctions is the composite of the two
inverse bijections.

This duplicates `CategoryTheory.Adjunction.comp_homEquiv_symm_apply` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/InverseImageComparison.lean`; it is
restated here under a different name so that this file depends only on Mathlib and on
`StacksFrontier/CategoryTheory/Sites/SliceTopos/OverPushforward.lean`. -/
theorem homEquiv_symm_comp_apply {F : C ⥤ D} {Gf : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ Gf) (adj₂ : H ⊣ I) (W : C) (Z : E) (g : W ⟶ (I ⋙ Gf).obj Z) :
    ((adj₁.comp adj₂).homEquiv W Z).symm g =
      (adj₂.homEquiv (F.obj W) Z).symm ((adj₁.homEquiv W (I.obj Z)).symm g) := by
  rw [Adjunction.comp_homEquiv]
  rfl

/-- A composite of four morphisms under a functor, with each of the four images named and the
first and last pairs already contracted.  This is the shape in which a structure map defined as a
four-fold composite is read on underlying sheaves of sets: two of the four factors are identities
there, so the two contractions are `CategoryTheory.Category.id_comp` and
`CategoryTheory.Category.comp_id`. -/
theorem map_comp_four {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F] (Φ : E ⥤ F)
    {A₀ A₁ A₂ A₃ A₄ : E} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    {p : Φ.obj A₀ ⟶ Φ.obj A₁} {q : Φ.obj A₁ ⟶ Φ.obj A₂} {r : Φ.obj A₂ ⟶ Φ.obj A₃}
    {s : Φ.obj A₃ ⟶ Φ.obj A₄} {t : Φ.obj A₀ ⟶ Φ.obj A₂} {w : Φ.obj A₂ ⟶ Φ.obj A₄}
    (ha : Φ.map a = p) (hb : Φ.map b = q) (hc : Φ.map c = r) (hd : Φ.map d = s)
    (hpq : p ≫ q = t) (hrs : r ≫ s = w) :
    Φ.map (a ≫ b ≫ c ≫ d) = t ≫ w := by
  rw [Φ.map_comp, Φ.map_comp, Φ.map_comp, ha, hb, hc, hd, ← hpq, ← hrs, Category.assoc]

/-- **Transporting an adjunction along an equality of left adjoints turns the comparison of right
adjoints into a conjugate.**  If `h : L = L'` and `adjP : L ⊣ RP`, `adjQ : L' ⊣ RQ`, then the two
adjunctions `adjQ` and `h ▸ adjP` have the same left adjoint, and the canonical comparison of
their right adjoints is the conjugate of `eqToHom h`. -/
theorem rightAdjointUniq_eqRec_hom {L L' : C ⥤ D} {RP RQ : D ⥤ C} (h : L = L')
    (adjP : L ⊣ RP) (adjQ : L' ⊣ RQ) :
    (Adjunction.rightAdjointUniq adjQ (h ▸ adjP : L' ⊣ RP)).hom =
      conjugateEquiv adjQ adjP (eqToHom h) := by
  subst h
  simp [Adjunction.rightAdjointUniq]

end Calculus

section Transport

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄} {E' : Type u₅} {F' : Type u₆}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  [Category.{v₅} E'] [Category.{v₆} F']
variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G' : C ⥤ E'} {H' : D ⥤ F'} {G₀ : C ⥤ E} {H₀ : D ⥤ F}

/-- **Mates are preserved by transport along equivalences.**  Let `α₀` be a 2-cell of the square
with verticals `G₀`, `H₀` and adjunctions `a : L₁ ⊣ R₁`, `b : L₂ ⊣ R₂`, and let `β₀` be its mate.
Replace `b` by its transport `(e.toAdjunction.comp b).comp g.symm.toAdjunction` along equivalences
`e : E' ≌ E` and `g : F' ≌ F`, and replace the verticals by functors `G'`, `H'` identified with
`G₀`, `H₀` after composing with `e.functor`, `g.functor`.  Then the correspondingly transported
2-cells `α` and `β` are again mates.

The hypotheses `hα` and `hβ` say that `α` and `β` *are* the transports: each is the given 2-cell
conjugated by the two comparison isomorphisms and the unit of the relevant equivalence. -/
theorem mateEquiv_transport (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : E' ≌ E) (g : F' ≌ F)
    (ivG : G' ⋙ e.functor ≅ G₀) (ivF : H' ⋙ g.functor ≅ H₀)
    (α₀ : TwoSquare G₀ L₁ L₂ H₀) (β₀ : TwoSquare R₁ H₀ G₀ R₂) (hm : mateEquiv a b α₀ = β₀)
    (α : TwoSquare G' L₁ ((e.functor ⋙ L₂) ⋙ g.inverse) H')
    (β : TwoSquare R₁ H' G' (g.functor ⋙ R₂ ⋙ e.inverse))
    (hα : ∀ W, α.natTrans.app W =
      g.inverse.map (L₂.map (ivG.hom.app W)) ≫ g.inverse.map (α₀.natTrans.app W) ≫
        g.inverse.map (ivF.inv.app (L₁.obj W)) ≫ g.unitIso.inv.app (H'.obj (L₁.obj W)))
    (hβ : ∀ d, β.natTrans.app d =
      e.unitIso.hom.app (G'.obj (R₁.obj d)) ≫ e.inverse.map (ivG.hom.app (R₁.obj d) ≫
        β₀.natTrans.app d ≫ R₂.map (ivF.inv.app d))) :
    mateEquiv a ((e.toAdjunction.comp b).comp g.symm.toAdjunction) α = β := by
  refine mateEquiv_eq_of_homEquiv_symm _ _ _ _ (fun d => ?_)
  rw [hβ d, hα (R₁.obj d), homEquiv_symm_comp_apply, homEquiv_symm_comp_apply,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have key : L₂.map (β₀.natTrans.app d) ≫ b.counit.app (H₀.obj d) =
      α₀.natTrans.app (R₁.obj d) ≫ H₀.map (a.counit.app d) :=
    hm ▸ mateEquiv_counit a b α₀ d
  have hT (T : e.functor.obj (G'.obj (R₁.obj d)) ⟶ R₂.obj (g.functor.obj (H'.obj d))) :
      e.functor.map (e.unitIso.hom.app (G'.obj (R₁.obj d)) ≫ e.inverse.map T) ≫
        e.counit.app (R₂.obj (g.functor.obj (H'.obj d))) = T := by simp
  have nat1 : L₂.map (R₂.map (ivF.inv.app d)) ≫ b.counit.app (g.functor.obj (H'.obj d)) =
      b.counit.app (H₀.obj d) ≫ ivF.inv.app d := b.counit_naturality _
  have nat2 : H₀.map (a.counit.app d) ≫ ivF.inv.app d =
      ivF.inv.app (L₁.obj (R₁.obj d)) ≫ g.functor.map (H'.map (a.counit.app d)) :=
    ivF.inv.naturality (a.counit.app d)
  have nat3 : g.inverse.map (g.functor.map (H'.map (a.counit.app d))) ≫
        g.unitInv.app (H'.obj d) =
      g.unitIso.inv.app (H'.obj (L₁.obj (R₁.obj d))) ≫ H'.map (a.counit.app d) :=
    g.unitIso.inv.naturality (H'.map (a.counit.app d))
  have s2 : L₂.map (ivG.hom.app (R₁.obj d) ≫ β₀.natTrans.app d ≫ R₂.map (ivF.inv.app d)) ≫
        b.counit.app (g.functor.obj (H'.obj d)) =
      L₂.map (ivG.hom.app (R₁.obj d)) ≫ α₀.natTrans.app (R₁.obj d) ≫
        ivF.inv.app (L₁.obj (R₁.obj d)) ≫ g.functor.map (H'.map (a.counit.app d)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, nat1,
      ← Category.assoc (L₂.map (β₀.natTrans.app d)), key, Category.assoc, nat2]
  simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit]
  rw [hT, s2, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Category.assoc, nat3]
  simp only [Category.assoc]

end Transport

end Stacks.CategoryTheory

namespace MorphismOfTopoi

universe v v' u u'

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]
  (f : MorphismOfTopoi E D) (G : D) [HasPullbacks D]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- **Stacks 04H1's inverse-image square is the mate of the lower-shriek identity.**  The third
face of the localization square, `(f')⁻¹ ⋙ j_{F!} = j_{G!} ⋙ f⁻¹`, holds on the nose
(`CategoryTheory.Over.post_forget_eq_forget_comp`); its mate across the two localization
adjunctions `j_! ⊣ j⁻¹`, which are `CategoryTheory.forgetAdjToOver`, is the inverse-image square
`MorphismOfTopoi.inverseImageCompToOverIso`.

On underlying objects the determining counit equation is that the comparison of `f⁻¹` with binary
products is compatible with the first projection. -/
theorem mateEquiv_eqToHom_post_forget :
    mateEquiv (forgetAdjToOver G) (forgetAdjToOver (f.inverseImage.obj G))
        (TwoSquare.mk (f.over G).inverseImage (Over.forget G)
          (Over.forget (f.inverseImage.obj G)) f.inverseImage
          (eqToHom (Over.post_forget_eq_forget_comp f.inverseImage G))) =
      TwoSquare.mk (toOver G) f.inverseImage (f.over G).inverseImage
        (toOver (f.inverseImage.obj G)) (f.inverseImageCompToOverIso G).inv := by
  have := f.preservesFiniteLimits
  let _ : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f.inverseImage
  refine Stacks.CategoryTheory.mateEquiv_eq_of_counit (forgetAdjToOver G)
    (forgetAdjToOver (f.inverseImage.obj G)) _ _ (fun A => ?_)
  have key : (Functor.Monoidal.μIso f.inverseImage A G).inv ≫
        fst (f.inverseImage.obj A) (f.inverseImage.obj G) = f.inverseImage.map (fst A G) := by
    rw [Iso.inv_comp_eq]
    exact (Functor.Monoidal.μ_fst f.inverseImage A G).symm
  have he : (eqToHom (Over.post_forget_eq_forget_comp f.inverseImage G) :
      (f.over G).inverseImage ⋙ Over.forget (f.inverseImage.obj G) ⟶
        Over.forget G ⋙ f.inverseImage).app ((toOver G).obj A) =
      𝟙 (f.inverseImage.obj (A ⊗ G)) := rfl
  simp only [forgetAdjToOver_counit_app, MorphismOfTopoi.inverseImageCompToOverIso,
    NatIso.ofComponents_inv_app, he]
  exact key.trans (Category.id_comp _).symm

/-- **Stacks 04H1's pushforward square is the Beck–Chevalley mate of its inverse-image square.**
Across the two vertical adjunctions `f⁻¹ ⊣ f_*` and `(f')⁻¹ ⊣ (f')_*` of the localization square,
the mate of `MorphismOfTopoi.inverseImageCompToOverIso` is
`MorphismOfTopoi.toOverCompPushforwardIso`, both read in the direction in which they compose.

All four functors of the square have left adjoints, so by
`CategoryTheory.iterated_mateEquiv_conjugateEquiv` taking mates twice is taking the conjugate; the
inner mate is `mateEquiv_eqToHom_post_forget` and the conjugate of the lower-shriek identity is
the comparison of right adjoints that `toOverCompPushforwardIso` is defined to be. -/
theorem mateEquiv_inverseImageCompToOverIso_inv :
    mateEquiv f.adj (f.over G).adj
        (TwoSquare.mk (toOver G) f.inverseImage (f.over G).inverseImage
          (toOver (f.inverseImage.obj G)) (f.inverseImageCompToOverIso G).inv) =
      TwoSquare.mk f.pushforward (toOver (f.inverseImage.obj G)) (toOver G)
        (f.over G).pushforward (f.toOverCompPushforwardIso G).inv := by
  refine Eq.trans
    (congrArg (mateEquiv f.adj (f.over G).adj)
      (f.mateEquiv_eqToHom_post_forget G)).symm ?_
  refine Eq.trans (iterated_mateEquiv_conjugateEquiv (forgetAdjToOver G)
    (forgetAdjToOver (f.inverseImage.obj G)) (f.over G).adj f.adj _) ?_
  exact TwoSquare.ext _ _ fun x =>
    (congrFun (congrArg NatTrans.app (Stacks.CategoryTheory.rightAdjointUniq_eqRec_hom
      (Over.post_forget_eq_forget_comp f.inverseImage G)
      ((f.over G).adj.comp (forgetAdjToOver (f.inverseImage.obj G)))
      ((forgetAdjToOver G).comp f.adj))) x).symm.trans
    (Adjunction.rightAdjointUniq_inv_app _ _ x).symm

end MorphismOfTopoi

end
