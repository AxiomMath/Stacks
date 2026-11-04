module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange

/-!
# Base change of the bijection between sections of a projective bundle and invertible quotients

Let `g : X ⟶ Y` be an arbitrary morphism of schemes and `E` a quasi-coherent `𝒪_Y`-module. Write
`π : 𝐏(E) ⟶ Y` and `π' : 𝐏(g^*E) ⟶ X` for the two projections and
`b : 𝐏(g^*E) ⟶ 𝐏(E)` for the base-change comparison morphism
`Stacks.RelativeProj.projectiveBundleBaseChange`, whose square with `π`, `π'` and `g` is
cartesian (`Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange`).

Tag 0B3V's last sentence asserts that its bijection between the sections of `π` and the
invertible quotients of `E` is compatible with base change. This file proves the half of that
sentence concerning the bijection, in the form of a commuting square: the forward map of the
bijection, `Stacks.RelativeProj.TautologicalDatum.sectionsMap`, carries the base change of a
section to the base change of the invertible quotient it classifies.

The left-hand vertical map is `Stacks.RelativeProj.sectionBaseChange`, the section of `π'`
obtained from a section of `π` by the universal property of the cartesian square — so it is
canonical and not a hypothesis. The right-hand vertical map is
`Stacks.ProjectiveBundleQuotients.baseChangeClass`, the pullback of invertible quotients on
isomorphism classes. The tautological datum on `𝐏(g^*E)` is the base-changed one,
`Stacks.RelativeProj.TautologicalDatum.baseChange`.

## Main definitions

* `Stacks.RelativeProj.sectionBaseChange`: the base change along `g` of a section of `π`, the
  morphism `X ⟶ 𝐏(g^*E)` induced by `𝟙 X` and `g ≫ σ` on the cartesian square.

## Main results

* `Stacks.Modules.pullbackComp_congr_assoc`: the associativity coherence of the pullback
  pseudofunctor on sheaves of modules, with the three composites carried as free variables so
  that it applies at a composite named in another way. This is the component form of
  `AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`.
* `Stacks.Modules.sectionSquare_coherence` and
  `Stacks.Modules.sectionSquare_coherence_inv`: **the two identifications of `g^*M` with
  `σ'^*b^*π^*M` agree**, for a section `σ` of `π`, a section `σ'` of `π'` lying over it, and a
  square `b ≫ π = π' ≫ g`. One goes through the section `σ'` and the comparison of
  `b^*π^*` with `π'^*g^*`; the other through the section `σ` and the comparison of `σ'^*b^*`
  with `g^*σ^*`. Stated for arbitrary schemes and morphisms, with no projective bundle in
  sight; it is exactly the pasting coherence of the pullback pseudofunctor at the two squares.
* `Stacks.RelativeProj.sectionBaseChange_comp_projectiveBundleToBase` and
  `Stacks.RelativeProj.sectionBaseChange_comp_projectiveBundleBaseChange`: the base-changed
  section is a section of `π'`, and it lies over the original one.
* `Stacks.RelativeProj.key_coherence`: the coherence above, at the projective bundle and its
  tautological base-change identification `Stacks.RelativeProj.tautologicalBaseChangeIso`.
* `Stacks.RelativeProj.classifies_sectionBaseChange`: **the base-changed section classifies the
  base change of the quotient classified by the original section.**
* `Stacks.RelativeProj.sectionsMap_sectionBaseChange`: **Tag 0B3V's bijection is compatible with
  base change**, as the commuting square described above.

## Implementation notes

**No `hE : E' ≅ g^*E` binder, and no hypothesis on `g` or on the rank of `E`.** The module on
the new base is literally `g^*E` and the comparison is the identity, which is the shape Tag 0B3V
states its base-change clause in. `Stacks.RelativeProj.projectiveBundleBaseChange` and
`Stacks.RelativeProj.TautologicalDatum.baseChange` both take the comparison as an argument, and
every use below passes `Iso.refl _`.

**The statement is about `sectionsMap`, not about
`Stacks.RelativeProj.TautologicalDatum.sectionsEquivInvertibleQuotients`.** `sectionsMap` is the
forward map of Tag 0B3V's bijection and is unconditional, whereas the bijection itself is only
available under `Stacks.RelativeProj.TautologicalDatum.IsUniversal`. Stating the square for
`sectionsMap` is therefore strictly stronger: it is the compatibility of the bijection with base
change wherever the bijection exists, and it assumes nothing about whether it does. In
particular nothing here is conditional on the bijectivity half of the tag.

**The tautological datum on `𝐏(E)` is a hypothesis.** The clause's own content is the commuting
square; which datum sits on `𝐏(E)` is not part of it, and the square is proved for every datum.

**The one declaration that is not formal bookkeeping is `sectionSquare_coherence`.** Everything
else is transport. Its proof is three instances of `pullbackComp_congr_assoc` — at the triples
`(g, σ, π)`, `(σ', b, π)` and `(σ', π', g)` — together with the two unitality coherences
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality` and `_right_unitality` of the
pullback pseudofunctor. The three composites that those three instances share are `g ≫ σ`,
`π' ≫ g` and `g` itself, and it is the two ways of reading `σ' ≫ b ≫ π` — as `(g ≫ σ) ≫ π`
and as `(σ' ≫ π') ≫ g`, both equal to `g` — that make the two routes agree.

**Why `Category.assoc` and `Functor.map_comp` are crossed in term mode.** The source of
`(Scheme.Modules.pullbackId X).inv.app M` is `(𝟭 X.Modules).obj M` rather than `M`, and
`(Stacks.RelativeProj.TautologicalDatum.baseChange g E E' hE D).twist` is
`(Scheme.Modules.pullback b).obj D.twist` only after unfolding the structure instance. Neither
is a syntactic match, so `rw` and `simp only` fail to find their patterns on the composites
below, while unification at default transparency succeeds. `Eq.trans`,
`CategoryTheory.whisker_eq` and the explicit `(Scheme.Modules.pullback g).map_comp` are used at
those three places; `ProjectiveBundle/TautologicalBaseChange.lean` records the same wall and the
same remedy.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {A B C D : Scheme.{u}}

/-- **Associativity of the pullback comparison of sheaves of modules**, in the form that carries
the three composites `f ≫ h`, `h ≫ k` and `(f ≫ h) ≫ k` as free variables together with their
identifications, so that it applies at a composite a consumer names in another way. Substituting
the three identifications reduces it to
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`. -/
theorem pullbackComp_congr_assoc (f : A ⟶ B) (h : B ⟶ C) (k : C ⟶ D)
    (c : A ⟶ C) (hc : f ≫ h = c) (d : B ⟶ D) (hd : h ≫ k = d) (e : A ⟶ D)
    (he : c ≫ k = e) (M : D.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp h k).hom.app M ≫
          (Scheme.Modules.pullbackCongr hd).hom.app M) ≫
        (Scheme.Modules.pullbackComp f d).hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (show f ≫ d = e by rw [← hd, ← hc, Category.assoc] at *; exact he)).hom.app M =
      ((Scheme.Modules.pullbackComp f h).hom.app ((Scheme.Modules.pullback k).obj M) ≫
          (Scheme.Modules.pullbackCongr hc).hom.app ((Scheme.Modules.pullback k).obj M)) ≫
        ((Scheme.Modules.pullbackComp c k).hom.app M ≫
          (Scheme.Modules.pullbackCongr he).hom.app M) := by
  subst hc hd he
  have key := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity (f := f) (g := h) (h := k)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at key
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_refl]
  rw [← key]
  simp

section Coherence

variable {X Y P P' : Scheme.{u}} (g : X ⟶ Y) (σ : Y ⟶ P) (π : P ⟶ Y) (σ' : X ⟶ P')
  (π' : P' ⟶ X) (b : P' ⟶ P)

/-- **The two routes from `g^*σ^*π^*M` to `g^*M` agree.** For a section `σ` of `π`, a section
`σ'` of `π'` with `σ' ≫ b = g ≫ σ`, and a square `b ≫ π = π' ≫ g`, one route uses the square
comparison of `σ'^*b^*` with `g^*σ^*`, the comparison of `b^*π^*` with `π'^*g^*` and the section
`σ'`; the other uses the section `σ` directly. No scheme here is a projective bundle: this is the
pasting coherence of the pullback pseudofunctor at the two squares. -/
theorem sectionSquare_coherence (hσ : σ ≫ π = 𝟙 Y) (hσ' : σ' ≫ π' = 𝟙 X)
    (hb : b ≫ π = π' ≫ g) (hbc : σ' ≫ b = g ≫ σ) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp g σ).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackCongr hbc).inv.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackComp σ' b).inv.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp b π).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackCongr hb).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ' π').hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ').hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp σ π).hom.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).hom.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app M) := by
  have he : (g ≫ σ) ≫ π = g := by rw [Category.assoc, hσ, Category.comp_id]
  have h1 := pullbackComp_congr_assoc g σ π (g ≫ σ) rfl (𝟙 Y) hσ g he M
  have h2 := pullbackComp_congr_assoc σ' b π (g ≫ σ) hbc (π' ≫ g) hb g he M
  have h3 := pullbackComp_congr_assoc σ' π' g (𝟙 X) hσ' (π' ≫ g) rfl g (Category.id_comp g) M
  have u1 := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_left_unitality (f := g)) M
  have u2 := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_right_unitality (f := g)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, eqToHom_app] at u1 u2
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Functor.map_comp, Category.assoc] at h1 h2 h3 ⊢
  have u1' : (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app M) =
      (Scheme.Modules.pullbackComp g (𝟙 Y)).hom.app M ≫ eqToHom (by simp) := by
    rw [← u1]
    simp
  have u2' : (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullbackComp (𝟙 X) g).hom.app M ≫ eqToHom (by simp) := by
    rw [← u2]
    simp
  rw [u1', u2', h1, ← h3]
  simp only [NatTrans.id_app]
  have cancel : ∀ {W : X.Modules}
      (t : (Scheme.Modules.pullback σ').obj ((Scheme.Modules.pullback (π' ≫ g)).obj M) ⟶ W),
      (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).inv.app M) ≫
          (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).hom.app M) ≫
          (Scheme.Modules.pullback σ').map
            (𝟙 ((Scheme.Modules.pullback (π' ≫ g)).obj M)) ≫ t = t := by
    intro W t
    rw [(Scheme.Modules.pullback σ').map_id, Category.id_comp, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, (Scheme.Modules.pullback σ').map_id, Category.id_comp]
  rw [cancel, h2]
  simp

/-- **The same coherence read in the other direction**, from `g^*M` to `g^*σ^*π^*M`, which is the
direction in which a quotient map pulled back along a section is written. Both composites are
isomorphisms, so this is `Stacks.Modules.sectionSquare_coherence` with every factor inverted. -/
theorem sectionSquare_coherence_inv (hσ : σ ≫ π = 𝟙 Y) (hσ' : σ' ≫ π' = 𝟙 X)
    (hb : b ≫ π = π' ≫ g) (hbc : σ' ≫ b = g ≫ σ) (M : Y.Modules) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ').inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp σ' π').inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackCongr hb).inv.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ' b).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackCongr hbc).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackComp g σ).inv.app ((Scheme.Modules.pullback π).obj M) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).inv.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp σ π).inv.app M) := by
  have tele : ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp σ π).hom.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).hom.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).hom.app M)) ≫
      ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).inv.app M) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackComp σ π).inv.app M)) = 𝟙 _ := by
    simp only [Category.assoc, ← Functor.map_comp]
    simp
  have tele' : ((Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ').inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp σ' π').inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackCongr hb).inv.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ' b).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackCongr hbc).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackComp g σ).inv.app ((Scheme.Modules.pullback π).obj M)) ≫
      ((Scheme.Modules.pullbackComp g σ).hom.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackCongr hbc).inv.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullbackComp σ' b).inv.app ((Scheme.Modules.pullback π).obj M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp b π).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackCongr hb).hom.app M) ≫
        (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullbackComp π' g).inv.app M) ≫
        (Scheme.Modules.pullbackComp σ' π').hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackCongr hσ').hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj M)) = 𝟙 _ := by
    simp
  rw [sectionSquare_coherence g σ π σ' π' b hσ hσ' hb hbc M] at tele'
  have gen : ∀ {A B : X.Modules} (p q : A ⟶ B) (k : B ⟶ A),
      p ≫ k = 𝟙 A → k ≫ q = 𝟙 B → p = q := by
    intro A B p q k h1 h2
    rw [← Category.comp_id p, ← h2, ← Category.assoc, h1, Category.id_comp]
  exact gen _ _ _ tele' tele

end Coherence

end Stacks.Modules

namespace Stacks.RelativeProj

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Y.Modules) [E.IsQuasicoherent]

/-- **The base change of a section of `π : 𝐏(E) ⟶ Y` along `g : X ⟶ Y`**: the morphism
`X ⟶ 𝐏(g^*E)` induced by `𝟙 X` and `g ≫ σ` on the cartesian square of
`Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange`. It is a section of `π'` and
lies over `σ`, and those two properties determine it. -/
def sectionBaseChange (σ : Y ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    X ⟶ projectiveBundle X ((Scheme.Modules.pullback g).obj E) :=
  (isPullback_projectiveBundleToBase_baseChange g E _ (Iso.refl _)).lift (𝟙 X) (g ≫ σ)
    (by rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

/-- The base change `sectionBaseChange g E σ hσ` is a section of the projection
`𝐏(g^*E) ⟶ X`. -/
@[simp] theorem sectionBaseChange_comp_projectiveBundleToBase
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    sectionBaseChange g E σ hσ ≫
        projectiveBundleToBase X ((Scheme.Modules.pullback g).obj E) = 𝟙 X :=
  (isPullback_projectiveBundleToBase_baseChange g E _ (Iso.refl _)).lift_fst _ _ _

/-- The base change `sectionBaseChange g E σ hσ` lies over `σ`: its composite with the
base-change morphism `𝐏(g^*E) ⟶ 𝐏(E)` is `g ≫ σ`. -/
@[simp] theorem sectionBaseChange_comp_projectiveBundleBaseChange
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    sectionBaseChange g E σ hσ ≫ projectiveBundleBaseChange g E _ (Iso.refl _) = g ≫ σ :=
  (isPullback_projectiveBundleToBase_baseChange g E _ (Iso.refl _)).lift_snd _ _ _

/-- **The coherence of `Stacks.Modules.sectionSquare_coherence_inv` at the projective bundle**:
the identification of `g^*E` with `σ'^*b^*π^*E` through the tautological base-change
identification `Stacks.RelativeProj.tautologicalBaseChangeIso` and the base-changed section
agrees with the one through `σ` and the square comparison of `σ'^*b^*` with `g^*σ^*`. -/
@[reassoc] theorem key_coherence (σ : Y ⟶ projectiveBundle Y E)
    (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackCongr
          (sectionBaseChange_comp_projectiveBundleToBase g E σ hσ)).inv.app
            ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (sectionBaseChange g E σ hσ)
          (projectiveBundleToBase X ((Scheme.Modules.pullback g).obj E))).inv.app
            ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullback (sectionBaseChange g E σ hσ)).map
          (tautologicalBaseChangeIso g E _ (Iso.refl _)).inv ≫
        (Stacks.Modules.pullbackSquareIso σ (sectionBaseChange g E σ hσ)
            (projectiveBundleBaseChange g E _ (Iso.refl _)) g
            (sectionBaseChange_comp_projectiveBundleBaseChange g E σ hσ).symm).hom.app
          ((Scheme.Modules.pullback (projectiveBundleToBase Y E)).obj E) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackId Y).inv.app E) ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullbackCongr hσ).inv.app E) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackComp σ (projectiveBundleToBase Y E)).inv.app E) := by
  simp only [Stacks.Modules.pullbackSquareIso, tautologicalBaseChangeIso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    Iso.refl_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [(Scheme.Modules.pullback (projectiveBundleToBase X
      ((Scheme.Modules.pullback g).obj E))).map_id,
    (Scheme.Modules.pullback (sectionBaseChange g E σ hσ)).map_id]
  simp only [Functor.comp_obj, Category.id_comp]
  exact Stacks.Modules.sectionSquare_coherence_inv g σ (projectiveBundleToBase Y E)
    (sectionBaseChange g E σ hσ)
    (projectiveBundleToBase X ((Scheme.Modules.pullback g).obj E))
    (projectiveBundleBaseChange g E _ (Iso.refl _)) hσ
    (sectionBaseChange_comp_projectiveBundleToBase g E σ hσ)
    (projectiveBundleBaseChange_comp_projectiveBundleToBase g E _ (Iso.refl _))
    (sectionBaseChange_comp_projectiveBundleBaseChange g E σ hσ) E


/-- **The base-changed section classifies the base change of the quotient classified by the
original section.** The comparison of quotient modules is the square comparison of `σ'^*b^*` with
`g^*σ^*` at the tautological module, and its compatibility with the two quotient maps is the
naturality of that comparison together with `Stacks.RelativeProj.key_coherence`. -/
theorem classifies_sectionBaseChange (D : TautologicalDatum Y E)
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    (D.baseChange g E _ (Iso.refl _)).Classifies (sectionBaseChange g E σ hσ)
      (sectionBaseChange_comp_projectiveBundleToBase g E σ hσ)
      (Stacks.ProjectiveBundleQuotients.InvertibleQuotient.baseChange g (Iso.refl _)
        (D.pullbackQuotient σ hσ)) := by
  let e := Stacks.Modules.pullbackSquareIso σ (sectionBaseChange g E σ hσ)
    (projectiveBundleBaseChange g E _ (Iso.refl _)) g
    (sectionBaseChange_comp_projectiveBundleBaseChange g E σ hσ).symm
  refine ⟨e.app D.twist, ?_⟩
  have hnat := e.hom.naturality D.univ
  simp only [TautologicalDatum.pullbackQuotient_q, TautologicalDatum.pullbackQuotientMap,
    Stacks.ProjectiveBundleQuotients.InvertibleQuotient.baseChange_q, Iso.refl_hom,
    Category.id_comp, Iso.app_hom]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (Category.assoc _ _ _))) ?_
  rw [TautologicalDatum.baseChange_univ]
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (Functor.map_comp_assoc _ _ _ _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ hnat)))) ?_
  refine Eq.trans (key_coherence_assoc _ _ _ _ _) ?_
  simp only [Functor.comp_map]
  exact (((Scheme.Modules.pullback g).map_comp _ _).trans
    ((whisker_eq _ ((Scheme.Modules.pullback g).map_comp _ _)).trans
      (whisker_eq _ (whisker_eq _ ((Scheme.Modules.pullback g).map_comp _ _))))).symm

/-- **Tag 0B3V: the bijection between the sections of `𝐏(ℰ) ⟶ X` and the invertible quotients
of `ℰ` is compatible with base change.** -/
theorem sectionsMap_sectionBaseChange (D : TautologicalDatum Y E)
    (σ : Y ⟶ projectiveBundle Y E) (hσ : σ ≫ projectiveBundleToBase Y E = 𝟙 Y) :
    (D.baseChange g E _ (Iso.refl _)).sectionsMap
        ⟨sectionBaseChange g E σ hσ,
          sectionBaseChange_comp_projectiveBundleToBase g E σ hσ⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass g (Iso.refl _) (D.sectionsMap ⟨σ, hσ⟩) :=
  ((D.baseChange g E _ (Iso.refl _)).sectionsMap_eq_iff _ _).2
    (classifies_sectionBaseChange g E D σ hσ)

end Stacks.RelativeProj

end
