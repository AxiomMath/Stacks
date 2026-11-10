module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings

/-!
# Morphisms between modules pulled back along a tower

Condition (4) of [Stacks, Tag 0EK2] is about the morphisms `𝒢|_{Y_n} ⟶ ℱ|_{Y_n}` between the
restrictions of two modules to the infinitesimal neighbourhoods of a closed subscheme, about the
inverse system they form, and about which of its compatible families come from a morphism
`𝒢|_W ⟶ ℱ|_W` defined on an open neighbourhood `W`. This file records those maps and the
resulting condition.

The identification needed to define them is the one already used to build
`AlgebraicGeometry.pullbackSectionsMap`: if `g ≫ b = a` then pulling a module back along `b` and
then along `g` is pulling it back along `a`.

## Main definitions

* `Stacks.Algebraization.pullbackObjFactorIso` — the identification `g^* (b^* M) ≅ a^* M` for
  `g ≫ b = a`, the component at one module of `Stacks.Algebraization.pullbackFactorIso`.
* `Stacks.Algebraization.pullbackHomMap` — the induced map on morphisms between pullbacks.
* `Stacks.Algebraization.homRestrict` — restriction of such a morphism to a smaller open.
* `Stacks.Algebraization.InfinitesimalTower.homAt` — the comparison of condition (4): a morphism
  of the restrictions to an open containing the support of a tower induces a morphism of the
  restrictions to each term of the tower.
* `Stacks.Algebraization.InfinitesimalTower.IsHomsComplete` — condition (4) for one pair of
  modules.

## Main results

* `Stacks.Algebraization.bijective_pullbackSectionsAt_ι` — for the inclusion of an open subscheme
  the comparison on the sections over that open is bijective, so the colimit side of the
  comparison may be read either as sections over the open or as global sections of the
  restriction.
* `Stacks.Algebraization.InfinitesimalTower.isHomsComplete_of_isSectionsComplete` and
  `Stacks.Algebraization.InfinitesimalTower.isSectionsComplete_of_isHomsComplete` — the
  bookkeeping shared by the implications `(3) ⇒ (4)` and `(4) ⇒ (3)`: an identification of the
  sections of one module with the morphisms between two others, compatible with shrinking the
  open and with the transition maps, turns either comparison into the other.

## Implementation notes

Everything is phrased with the structure morphisms written out and a factorization equation
supplied, rather than with objects and morphisms of `CategoryTheory.Over Z`. The reason is a
performance cliff: `AlgebraicGeometry.Scheme.Modules.pullback` is built from the sheafification of
a comparison of presheaves of modules, and deciding `(Over.mk f).hom =?= f` inside its argument
exhausts the elaborator's budget. Taking the morphism itself as the argument means the question is
never asked. The morphisms of `Over Z` that do occur — the transitions of a tower — are consumed
through `CategoryTheory.Over.w`, which is an equation between morphisms and so costs nothing.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

/-- If `g ≫ b = a` then pulling a module on `Z` back along `b` and then along `g` is pulling it
back along `a`: the component at one module of the comparison
`Stacks.Algebraization.pullbackFactorIso` of the two functors. -/
public def pullbackObjFactorIso {Z : Scheme.{u}} (M : Z.Modules) {A B : Scheme.{u}} {a : A ⟶ Z}
    {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback a).obj M :=
  (pullbackFactorIso b g a hg).app M

/-- The induced map on morphisms between pullbacks, for a factorization `g ≫ b = a`. -/
public def pullbackHomMap {Z : Scheme.{u}} (G F : Z.Modules) {A B : Scheme.{u}} {a : A ⟶ Z}
    {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
    (ψ : (Scheme.Modules.pullback b).obj G ⟶ (Scheme.Modules.pullback b).obj F) :
    (Scheme.Modules.pullback a).obj G ⟶ (Scheme.Modules.pullback a).obj F :=
  (pullbackObjFactorIso G g hg).inv ≫
    (Scheme.Modules.pullback g).map ψ ≫ (pullbackObjFactorIso F g hg).hom

/-- Restriction to a smaller open of a morphism between the restrictions of two modules. -/
public def homRestrict {Z : Scheme.{u}} (G F : Z.Modules) {W W' : Z.Opens} (h : W' ≤ W)
    (φ : (Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F) :
    (Scheme.Modules.pullback W'.ι).obj G ⟶ (Scheme.Modules.pullback W'.ι).obj F :=
  pullbackHomMap G F (Z.homOfLE h) (Z.homOfLE_ι h) φ

/-- Restriction along an equality of opens is an isomorphism on sections. -/
public instance isIso_presheaf_map_eqToHom {Z : Scheme.{u}} (M : Z.Modules) {U V : Z.Opens}
    (e : U = V) : IsIso (M.presheaf.map (eqToHom e).op) :=
  inferInstanceAs (IsIso (M.presheaf.mapIso (eqToIso e).op).hom)

/-- Evaluating an isomorphism of modules at an open gives a bijection on sections. -/
public theorem bijective_app_of_isIso {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) [IsIso φ]
    (W : Z.Opens) : Function.Bijective (φ.app W) := by
  have : IsIso (φ.app W) := by
    change IsIso (((Scheme.Modules.toPresheaf Z).map φ).app (.op W))
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

/-- **The sections of a module over an open are the global sections of its restriction.** For the
inclusion of an open subscheme `W` the comparison `AlgebraicGeometry.pullbackSectionsAt` on the
sections over `W` is bijective. -/
public theorem bijective_pullbackSectionsAt_ι {Z : Scheme.{u}} (W : Z.Opens) (M : Z.Modules)
    (h : W.ι ⁻¹ᵁ W = ⊤) : Function.Bijective (pullbackSectionsAt W.ι M h) := by
  have himg : W.ι ''ᵁ (W.ι ⁻¹ᵁ W) = W := by rw [h]; exact W.ι_image_top
  have h1 : IsIso (((Scheme.Modules.restrictAdjunction W.ι).unit.app M).app W) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have he : (homOfLE (W.ι.image_preimage_le W) : (W.ι ''ᵁ (W.ι ⁻¹ᵁ W)) ⟶ W) =
        eqToHom himg := Subsingleton.elim _ _
    rw [he]
    exact isIso_presheaf_map_eqToHom M himg
  have h2 : IsIso (((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app M)).app W) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_app_of_isIso _ W
  have key := (Scheme.Modules.restrictAdjunction W.ι).unit_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction W.ι) M
  have hunit := congrArg (fun χ => Scheme.Modules.Hom.app χ W) key
  have h3 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).app W) := by
    rw [← hunit, Scheme.Modules.Hom.comp_app]
    exact IsIso.comp_isIso
  have hb1 := (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).app W)).1 h3
  have hb2 := (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pullback W.ι).obj M).presheaf.map (eqToHom h.symm).op)).1
      (isIso_presheaf_map_eqToHom ((Scheme.Modules.pullback W.ι).obj M) h.symm)
  have hcomp : ∀ x : Γ(M, W), pullbackSectionsAt W.ι M h x =
      ((Scheme.Modules.pullback W.ι).obj M).presheaf.map (eqToHom h.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).app W x) :=
    fun x => ConcreteCategory.comp_apply _ _ x
  refine ⟨fun x y hxy => hb1.1 (hb2.1 ?_), fun z => ?_⟩
  · rw [← hcomp, ← hcomp]; exact hxy
  · obtain ⟨y, hy⟩ := hb2.2 z
    obtain ⟨x, hx⟩ := hb1.2 y
    exact ⟨x, by rw [hcomp, hx, hy]⟩

namespace InfinitesimalTower

variable {Z : Scheme.{u}} (T : InfinitesimalTower Z)

/-- The structure morphism of a term of the tower factors through any open containing the
support. -/
public def homToOpen {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ) :
    (T.obj n).left ⟶ W.toScheme :=
  liftToOpen (T.obj n).hom W fun _ hx => hW (T.range_hom_subset n hx)

/-- The factorization of the structure morphism through the open. -/
public theorem homToOpen_ι {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ) :
    T.homToOpen hW n ≫ W.ι = (T.obj n).hom :=
  liftToOpen_ι (T.obj n).hom W fun _ hx => hW (T.range_hom_subset n hx)

/-- **The comparison of condition (4) of [Stacks, Tag 0EK2].** A morphism of the restrictions of
`G` and `F` to an open neighbourhood `W` of the support induces a morphism of their restrictions
to each term of the tower. -/
public def homAt (G F : Z.Modules) {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ)
    (φ : (Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F) :
    (Scheme.Modules.pullback (T.obj n).hom).obj G ⟶
      (Scheme.Modules.pullback (T.obj n).hom).obj F :=
  pullbackHomMap G F (T.homToOpen hW n) (T.homToOpen_ι hW n) φ

/-- The transition maps of the inverse system of morphisms on the terms of the tower. -/
public def homTrans (G F : Z.Modules) (n m : ℕ) (h : n ≤ m)
    (ψ : (Scheme.Modules.pullback (T.obj m).hom).obj G ⟶
      (Scheme.Modules.pullback (T.obj m).hom).obj F) :
    (Scheme.Modules.pullback (T.obj n).hom).obj G ⟶
      (Scheme.Modules.pullback (T.obj n).hom).obj F :=
  pullbackHomMap G F (T.trans n m h).left (Over.w (T.trans n m h)) ψ

/-- **Condition (4) of [Stacks, Tag 0EK2] for one pair of modules.** The colimit of the morphisms
`G|_W ⟶ F|_W` over the open neighbourhoods `W` of the support is the inverse limit of the
morphisms `G|_{Y_n} ⟶ F|_{Y_n}`: every compatible family of the latter comes from a morphism on
some neighbourhood, and two morphisms on neighbourhoods inducing the same family agree on a
smaller neighbourhood. -/
public structure IsHomsComplete (G F : Z.Modules) : Prop where
  /-- Every compatible family of morphisms on the terms of the tower comes from a morphism of the
  restrictions to some open containing the support. -/
  exists_hom : ∀ ψ : ∀ n : ℕ, ((Scheme.Modules.pullback (T.obj n).hom).obj G ⟶
        (Scheme.Modules.pullback (T.obj n).hom).obj F),
      (∀ (n m : ℕ) (h : n ≤ m), T.homTrans G F n m h (ψ m) = ψ n) →
      ∃ (W : Z.Opens) (hW : T.support ⊆ W)
        (φ : (Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F),
        ∀ n : ℕ, T.homAt G F hW n φ = ψ n
  /-- Two morphisms of restrictions inducing the same family on the terms of the tower agree after
  shrinking the open. -/
  eq_of_homAt_eq : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W')
      (φ : (Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F)
      (φ' : (Scheme.Modules.pullback W'.ι).obj G ⟶ (Scheme.Modules.pullback W'.ι).obj F),
      (∀ n : ℕ, T.homAt G F hW n φ = T.homAt G F hW' n φ') →
      ∃ (W'' : Z.Opens) (_ : T.support ⊆ W'') (h₁ : W'' ≤ W) (h₂ : W'' ≤ W'),
        homRestrict G F h₁ φ = homRestrict G F h₂ φ'

/-- **Condition (3) for one module gives condition (4) for a pair, through an identification of
the sections with the morphisms.** Suppose the sections of `E` over the opens containing the
support are identified with the morphisms `G|_W ⟶ F|_W`, compatibly with shrinking the open; that
the sections of `E` on the terms of the tower are identified with the morphisms `G|_n ⟶ F|_n`,
compatibly with the transition maps; and that the two identifications intertwine the two
comparisons. Then the comparison for `E` is the comparison for the pair `(G, F)`.

This is the bookkeeping shared by the two implications `(3) ⇒ (4)` and `(4) ⇒ (3)` of
[Stacks, Tag 0EK2]: the former applies it with `E` the internal hom `ℋom(G, F)`, the latter with
`G` the structure sheaf and `E = F`. -/
public theorem isHomsComplete_of_isSectionsComplete (E G F : Z.Modules)
    (γ : ∀ W : Z.Opens, T.support ⊆ W →
      Γ(E, W) → ((Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F))
    (hγ : ∀ (W : Z.Opens) (hW : T.support ⊆ W), Function.Bijective (γ W hW))
    (hγres : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W') (h : W' ≤ W)
      (t : Γ(E, W)),
      γ W' hW' (E.presheaf.map (homOfLE h).op t) = homRestrict G F h (γ W hW t))
    (δ : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤) →
      ((Scheme.Modules.pullback (T.obj n).hom).obj G ⟶
        (Scheme.Modules.pullback (T.obj n).hom).obj F))
    (hδ : ∀ n : ℕ, Function.Bijective (δ n))
    (hδtrans : ∀ (n m : ℕ) (h : n ≤ m)
      (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)),
      δ n (pullbackSectionsMap E (T.trans n m h) x) = T.homTrans G F n m h (δ m x))
    (hcompat : ∀ (W : Z.Opens) (hW : T.support ⊆ W) (n : ℕ) (t : Γ(E, W)),
      δ n (T.sectionsAt E hW n t) = T.homAt G F hW n (γ W hW t))
    (hE : T.IsSectionsComplete E) : T.IsHomsComplete G F where
  exists_hom := by
    intro ψ hψ
    have hinv : ∀ (n : ℕ) (y : _), δ n (Function.surjInv (hδ n).2 y) = y :=
      fun n y => Function.surjInv_eq (hδ n).2 y
    obtain ⟨W, hW, t, ht⟩ := hE.exists_section (fun n => Function.surjInv (hδ n).2 (ψ n))
      (fun n m h => (hδ n).1 (by rw [hδtrans n m h _, hinv m (ψ m), hψ n m h, hinv n (ψ n)]))
    refine ⟨W, hW, γ W hW t, fun n => ?_⟩
    rw [← hcompat W hW n t, ht n]
    exact hinv n (ψ n)
  eq_of_homAt_eq := by
    intro W W' hW hW' φ φ' hφ
    obtain ⟨W'', hW'', h₁, h₂, hres⟩ := hE.eq_of_sectionsAt_eq W W' hW hW'
      (Function.surjInv (hγ W hW).2 φ) (Function.surjInv (hγ W' hW').2 φ') (fun n =>
        (hδ n).1 (by
          rw [hcompat W hW n _, hcompat W' hW' n _, Function.surjInv_eq (hγ W hW).2 φ,
            Function.surjInv_eq (hγ W' hW').2 φ', hφ n]))
    refine ⟨W'', hW'', h₁, h₂, ?_⟩
    have hr : ∀ (U : Z.Opens) (hU : T.support ⊆ U) (h : W'' ≤ U) (ψ : _),
        homRestrict G F h ψ =
          γ W'' hW'' (E.presheaf.map (homOfLE h).op (Function.surjInv (hγ U hU).2 ψ)) := by
      intro U hU h ψ
      rw [hγres U W'' hU hW'' h, Function.surjInv_eq (hγ U hU).2 ψ]
    rw [hr W hW h₁ φ, hr W' hW' h₂ φ', hres]

/-- **Condition (4) for a pair gives condition (3) for one module**, through the same
identification of the sections with the morphisms as
`Stacks.Algebraization.InfinitesimalTower.isHomsComplete_of_isSectionsComplete`. This is the
direction the implication `(4) ⇒ (3)` of [Stacks, Tag 0EK2] is read in, with `G` the structure
sheaf. -/
public theorem isSectionsComplete_of_isHomsComplete (E G F : Z.Modules)
    (γ : ∀ W : Z.Opens, T.support ⊆ W →
      Γ(E, W) → ((Scheme.Modules.pullback W.ι).obj G ⟶ (Scheme.Modules.pullback W.ι).obj F))
    (hγ : ∀ (W : Z.Opens) (hW : T.support ⊆ W), Function.Bijective (γ W hW))
    (hγres : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W') (h : W' ≤ W)
      (t : Γ(E, W)),
      γ W' hW' (E.presheaf.map (homOfLE h).op t) = homRestrict G F h (γ W hW t))
    (δ : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤) →
      ((Scheme.Modules.pullback (T.obj n).hom).obj G ⟶
        (Scheme.Modules.pullback (T.obj n).hom).obj F))
    (hδ : ∀ n : ℕ, Function.Bijective (δ n))
    (hδtrans : ∀ (n m : ℕ) (h : n ≤ m)
      (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)),
      δ n (pullbackSectionsMap E (T.trans n m h) x) = T.homTrans G F n m h (δ m x))
    (hcompat : ∀ (W : Z.Opens) (hW : T.support ⊆ W) (n : ℕ) (t : Γ(E, W)),
      δ n (T.sectionsAt E hW n t) = T.homAt G F hW n (γ W hW t))
    (hGF : T.IsHomsComplete G F) : T.IsSectionsComplete E where
  exists_section := by
    intro s hs
    obtain ⟨W, hW, φ, hφ⟩ := hGF.exists_hom (fun n => δ n (s n)) (fun n m h =>
      (hδtrans n m h (s m)).symm.trans (congrArg (δ n) (hs n m h)))
    refine ⟨W, hW, Function.surjInv (hγ W hW).2 φ, fun n => ?_⟩
    refine (hδ n).1 ?_
    rw [hcompat W hW n _, Function.surjInv_eq (hγ W hW).2 φ, hφ n]
  eq_of_sectionsAt_eq := by
    intro W W' hW hW' t u htu
    obtain ⟨W'', hW'', h₁, h₂, hres⟩ := hGF.eq_of_homAt_eq W W' hW hW'
      (γ W hW t) (γ W' hW' u) (fun n =>
        (hcompat W hW n t).symm.trans ((congrArg (δ n) (htu n)).trans (hcompat W' hW' n u)))
    refine ⟨W'', hW'', h₁, h₂, (hγ W'' hW'').1 ?_⟩
    rw [hγres W W'' hW hW'' h₁ t, hγres W' W'' hW' hW'' h₂ u, hres]

end InfinitesimalTower

end Stacks.Algebraization

end
