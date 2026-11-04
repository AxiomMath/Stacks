module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport

/-!
# Relative limit preservation and fibre products of presheaves

Relative limit preservation of a transformation of presheaves on the big fppf site over a
scheme is stable under base change: the first projection of a fibre product of presheaves
is relatively limit preserving as soon as the transformation it is based from is. The same
computation gives relative limit preservation for the map from a fibre product of two
presheaves over a common target presheaf.

## Main results

* `AlgebraicGeometry.relativelyLimitPreserving_pullback_fst` is stability under base
  change.
* `AlgebraicGeometry.relativelyLimitPreserving_pullback` treats a fibre product over a
  common intermediate presheaf.

## Implementation notes

The fibre product of presheaves is the pointwise pullback in the functor category, so the
section fibre of a base-changed transformation is isomorphic to the section fibre of the
original at the image section; that isomorphism is what transports limit preservation. For
the fibre product the section fibres themselves form a cartesian square at every object,
and a filtered colimit of cartesian squares of sets is cartesian, which identifies the
comparison cocone of the fibre product's section fibre as a colimit.

## References

* [Stacks Project, Tag 049M](https://stacks.math.columbia.edu/tag/049M)
* [Stacks Project, Tag 0GDZ](https://stacks.math.columbia.edu/tag/0GDZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- At each object, the fibre of the first projection of a fibre product of presheaves over
a section of the third presheaf is in bijection with the fibre of the base transformation
over the image of that section. -/
private noncomputable def sectionFiberPullbackEquiv
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G)
    (X : BigFppfOver B S hS)
    (y : H.obj (Opposite.op X)) (Y : (Over X)ᵒᵖ) :
    {p : (pullback b a).obj (Opposite.op Y.unop.left) //
      (pullback.fst b a).app (Opposite.op Y.unop.left) p =
        H.map Y.unop.hom.op y} ≃
    {x : F.obj (Opposite.op Y.unop.left) //
      a.app (Opposite.op Y.unop.left) x =
        G.map Y.unop.hom.op (b.app (Opposite.op X) y)} := by
  let d := Opposite.op Y.unop.left
  let e := pullbackObjIso b a d
  let t := Types.pullbackIsoPullback (b.app d) (a.app d)
  refine
    { toFun := fun p => ?_
      invFun := fun x => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let z := t.hom (e.hom p.1)
    refine ⟨z.1.2, ?_⟩
    have hz : z.1.1 = (pullback.fst b a).app d p.1 := by
      change ((Types.pullbackIsoPullback (b.app d) (a.app d)).hom
        ((pullbackObjIso b a d).hom p.1)).1.1 = _
      calc
        _ = pullback.fst (b.app d) (a.app d) ((pullbackObjIso b a d).hom p.1) :=
          Types.pullbackIsoPullback_hom_fst _ _ _
        _ = (pullback.fst b a).app d p.1 := by
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun k => k p.1) (pullbackObjIso_hom_comp_fst b a d)
    calc
      a.app d z.1.2 = b.app d z.1.1 := z.2.symm
      _ = b.app d (H.map Y.unop.hom.op y) := by rw [hz, p.2]
      _ = G.map Y.unop.hom.op (b.app (Opposite.op X) y) := by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (fun k => k y) (b.naturality Y.unop.hom.op)
  · let z : Types.PullbackObj (b.app d) (a.app d) :=
      ⟨⟨H.map Y.unop.hom.op y, x.1⟩, by
        calc
          b.app d (H.map Y.unop.hom.op y) = G.map Y.unop.hom.op (b.app (Opposite.op X) y) := by
            simpa only [ConcreteCategory.comp_apply] using
              congrArg (fun k => k y) (b.naturality Y.unop.hom.op)
          _ = a.app d x.1 := x.2.symm⟩
    refine ⟨e.inv (t.inv z), ?_⟩
    change (pullback.fst b a).app d
      ((pullbackObjIso b a d).inv ((Types.pullbackIsoPullback (b.app d) (a.app d)).inv z)) = _
    calc
      _ = pullback.fst (b.app d) (a.app d)
          ((Types.pullbackIsoPullback (b.app d) (a.app d)).inv z) := by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (fun k => k ((Types.pullbackIsoPullback (b.app d) (a.app d)).inv z))
            (pullbackObjIso_inv_comp_fst b a d)
      _ = z.1.1 := by
        have hf := congrArg (fun k => k z) (Types.pullbackIsoPullback_inv_fst (b.app d) (a.app d))
        change _ = z.1.1 at hf
        simpa only [ConcreteCategory.comp_apply] using hf
  · intro p
    apply Subtype.ext
    apply e.toEquiv.injective
    apply t.toEquiv.injective
    apply Subtype.ext
    simp only [Iso.toEquiv_apply, Iso.inv_hom_id_apply]
    apply Prod.ext
    · calc
        H.map Y.unop.hom.op y = (pullback.fst b a).app d p.1 := p.2.symm
        _ = pullback.fst (b.app d) (a.app d) ((pullbackObjIso b a d).hom p.1) := by
          simpa only [ConcreteCategory.comp_apply] using
            (congrArg (fun k => k p.1) (pullbackObjIso_hom_comp_fst b a d)).symm
    · simp [e, t]
  · intro x
    apply Subtype.ext
    simp [e, t]

/-- The bijection `sectionFiberPullbackEquiv` is given by the second pullback projection. -/
private theorem sectionFiberPullbackEquiv_val
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G)
    (X : BigFppfOver B S hS)
    (y : H.obj (Opposite.op X)) (Y : (Over X)ᵒᵖ)
    (p : (sectionFiber B S hS (pullback.fst b a) X y).obj Y) :
    (sectionFiberPullbackEquiv B S hS a b X y Y p).1 =
      (pullback.snd b a).app (Opposite.op Y.unop.left) p.1 := by
  show ((Types.pullbackIsoPullback
    (b.app (Opposite.op Y.unop.left)) (a.app (Opposite.op Y.unop.left))).hom
      ((pullbackObjIso b a (Opposite.op Y.unop.left)).hom p.1)).1.2 = _
  calc
    _ = pullback.snd (b.app (Opposite.op Y.unop.left))
        (a.app (Opposite.op Y.unop.left))
        ((pullbackObjIso b a (Opposite.op Y.unop.left)).hom p.1) :=
      Types.pullbackIsoPullback_hom_snd _ _ _
    _ = (pullback.snd b a).app (Opposite.op Y.unop.left) p.1 := by
      simpa only [ConcreteCategory.comp_apply] using
        congrArg (fun k => k p.1) (pullbackObjIso_hom_comp_snd b a (Opposite.op Y.unop.left))

/-- The section fibre of the first projection of a fibre product of presheaves is isomorphic
to the section fibre of the base transformation at the image section. -/
private noncomputable def sectionFiberPullbackIso
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G)
    (X : BigFppfOver B S hS)
    (y : H.obj (Opposite.op X)) :
    sectionFiber B S hS (pullback.fst b a) X y ≅
      sectionFiber B S hS a X (b.app (Opposite.op X) y) := by
  refine NatIso.ofComponents (fun Y => (sectionFiberPullbackEquiv B S hS a b X y Y).toIso) ?_
  intro Y Z f
  ext x
  apply Subtype.ext
  change (sectionFiberPullbackEquiv B S hS a b X y Z
      ((sectionFiber B S hS (pullback.fst b a) X y).map f x)).1 =
    F.map f.unop.left.op ((sectionFiberPullbackEquiv B S hS a b X y Y x).1)
  rw [sectionFiberPullbackEquiv_val, sectionFiberPullbackEquiv_val]
  simp [sectionFiber]

/-- A relatively limit-preserving transformation of presheaves remains so
after pullback along any transformation. -/
@[stacks 049M]
public theorem relativelyLimitPreserving_pullback_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G)
    (ha : RelativelyLimitPreserving.{u, v, w, w'} B S hS a) :
    RelativelyLimitPreserving.{u, v, w, w'} B S hS
      (pullback.fst b a) := by
  intro X y
  exact limitPreserving_of_natIso (sectionFiberPullbackIso B S hS a b X y).symm
    (ha X (b.app (Opposite.op X) y))

/-- A filtered colimit of cartesian squares of sets is cartesian: if a square of diagrams is
cartesian at every index, and the three outer diagrams have colimits forming a cartesian
square with the given cocone, then that cocone is a colimit. -/
private theorem filteredColimitOfPullbackSquares
    {I : Type w} [Category.{w'} I] [IsFilteredOrEmpty I]
    {P F G H : I ⥤ Type v} (pF : P ⟶ F) (pH : P ⟶ H)
    (α : F ⟶ G) (β : H ⟶ G)
    {cP : Cocone P} {cF : Cocone F} {cG : Cocone G} {cH : Cocone H}
    (qF : cP.pt ⟶ cF.pt) (qH : cP.pt ⟶ cH.pt)
    (f₀ : cF.pt ⟶ cG.pt) (g₀ : cH.pt ⟶ cG.pt)
    (hF : IsColimit cF) (hG : IsColimit cG) (hH : IsColimit cH)
    (hP : ∀ i, IsPullback (pF.app i) (pH.app i) (α.app i) (β.app i))
    (hPt : IsPullback qF qH f₀ g₀)
    (hPF : ∀ i, pF.app i ≫ cF.ι.app i = cP.ι.app i ≫ qF)
    (hPH : ∀ i, pH.app i ≫ cH.ι.app i = cP.ι.app i ≫ qH)
    (hFG : ∀ i, α.app i ≫ cG.ι.app i = cF.ι.app i ≫ f₀)
    (hHG : ∀ i, β.app i ≫ cG.ι.app i = cH.ι.app i ≫ g₀) :
    Nonempty (IsColimit cP) := by
  refine ⟨?_⟩
  apply Types.FilteredColimit.isColimitOf' P cP
  · intro z
    obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hF (qF z)
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hH (qH z)
    obtain ⟨k, u, v, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    let xk := F.map u x
    let yk := H.map v y
    have hg : cG.ι.app k (α.app k xk) = cG.ι.app k (β.app k yk) := by
      calc
        cG.ι.app k (α.app k xk) = (f₀ ∘ cF.ι.app k) xk := by
          simpa [Category.comp_apply] using congrArg (fun φ => φ xk) (hFG k)
        _ = f₀ (cF.ι.app i x) := by simp [xk]
        _ = f₀ (qF z) := by rw [hx]
        _ = g₀ (qH z) := by
          simpa [Category.comp_apply] using congrArg (fun φ => φ z) hPt.w
        _ = g₀ (cH.ι.app j y) := by rw [hy]
        _ = (g₀ ∘ cH.ι.app k) yk := by simp [yk]
        _ = cG.ι.app k (β.app k yk) := by
          simpa [Category.comp_apply] using (congrArg (fun φ => φ yk) (hHG k)).symm
    obtain ⟨l, f, g, heq⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff (F := G) hG).mp hg
    have hpull : α.app l (F.map f xk) = β.app l (H.map g yk) := by
      simpa using heq
    obtain ⟨zₗ, hzF, hzH⟩ := Types.exists_of_isPullback (hP l)
      (F.map f xk) (H.map g yk) hpull
    refine ⟨l, zₗ, ?_⟩
    have hqF : qF (cP.ι.app l zₗ) = qF z := by
      calc
        qF (cP.ι.app l zₗ) = cF.ι.app l (pF.app l zₗ) := by
          simpa [Category.comp_apply] using (congrArg (fun φ => φ zₗ) (hPF l)).symm
        _ = cF.ι.app l (F.map f xk) := by rw [hzF]
        _ = cF.ι.app i x := by simp [xk]
        _ = qF z := hx
    have hqH : qH (cP.ι.app l zₗ) = qH z := by
      calc
        qH (cP.ι.app l zₗ) = cH.ι.app l (pH.app l zₗ) := by
          simpa [Category.comp_apply] using (congrArg (fun φ => φ zₗ) (hPH l)).symm
        _ = cH.ι.app l (H.map g yk) := by rw [hzH]
        _ = cH.ι.app j y := by simp [yk]
        _ = qH z := hy
    exact Types.ext_of_isPullback hPt hqF.symm hqH.symm
  · intro i x y hxy
    have hxF : cF.ι.app i (pF.app i x) = cF.ι.app i (pF.app i y) := by
      calc
        cF.ι.app i (pF.app i x) = qF (cP.ι.app i x) := by
          simpa [Category.comp_apply] using congrArg (fun φ => φ x) (hPF i)
        _ = qF (cP.ι.app i y) := by rw [hxy]
        _ = cF.ι.app i (pF.app i y) := by
          simpa [Category.comp_apply] using (congrArg (fun φ => φ y) (hPF i)).symm
    have hxH : cH.ι.app i (pH.app i x) = cH.ι.app i (pH.app i y) := by
      calc
        cH.ι.app i (pH.app i x) = qH (cP.ι.app i x) := by
          simpa [Category.comp_apply] using congrArg (fun φ => φ x) (hPH i)
        _ = qH (cP.ι.app i y) := by rw [hxy]
        _ = cH.ι.app i (pH.app i y) := by
          simpa [Category.comp_apply] using (congrArg (fun φ => φ y) (hPH i)).symm
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (F := F) hF (i := i) _ _).mp hxF
    obtain ⟨k, g, hg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (F := H) hH (i := i) _ _).mp hxH
    obtain ⟨m, u, v, _⟩ := IsFilteredOrEmpty.cocone_objs j k
    obtain ⟨n, t, ht⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ u) (g ≫ v)
    let l₁ := f ≫ u ≫ t
    let l₂ := g ≫ v ≫ t
    have hl : l₁ = l₂ := by
      dsimp [l₁, l₂]
      simpa [Category.assoc] using ht
    have hpF : pF.app n (P.map l₁ x) = pF.app n (P.map l₂ y) := by
      calc
        pF.app n (P.map l₁ x) = F.map l₁ (pF.app i x) := by simp
        _ = F.map l₁ (pF.app i y) := by
          dsimp [l₁]
          simpa only [Functor.map_comp_apply] using congrArg (F.map (u ≫ t)) hf
        _ = F.map l₂ (pF.app i y) := by rw [hl]
        _ = pF.app n (P.map l₂ y) := by simp
    have hpH : pH.app n (P.map l₁ x) = pH.app n (P.map l₂ y) := by
      calc
        pH.app n (P.map l₁ x) = H.map l₁ (pH.app i x) := by simp
        _ = H.map l₂ (pH.app i x) := by rw [hl]
        _ = H.map l₂ (pH.app i y) := by
          dsimp [l₂]
          simpa only [Functor.map_comp_apply] using congrArg (H.map (v ≫ t)) hg
        _ = pH.app n (P.map l₂ y) := by simp
    exact ⟨n, l₁, by simpa [hl] using Types.ext_of_isPullback (hP n) hpF hpH⟩

/-- Composing with a transformation on the left maps the section fibre of the composite into
the section fibre of the second factor, over the same target section. -/
private def sectionFiberPrecomp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (f : F ⟶ G) (g : G ⟶ E) (X : BigFppfOver B S hS)
    (y : E.obj (Opposite.op X)) :
    sectionFiber B S hS (f ≫ g) X y ⟶
      sectionFiber B S hS g X y where
  app Y := TypeCat.ofHom fun x => ⟨f.app (Opposite.op Y.unop.left) x.1, by
    simpa [Functor.comp_apply] using x.2⟩
  naturality := by
    intro Y Z φ
    ext x
    simp [sectionFiber]

/-- The second pullback projection maps the section fibre of the composite through the first
projection into the section fibre of the composite through the second one. -/
private noncomputable def sectionFiberPullbackRight
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) (c : G ⟶ E)
    (X : BigFppfOver B S hS) (y : E.obj (Opposite.op X)) :
    sectionFiber B S hS (pullback.fst a b ≫ a ≫ c) X y ⟶
      sectionFiber B S hS (b ≫ c) X y where
  app Y := TypeCat.ofHom fun x => ⟨(pullback.snd a b).app (Opposite.op Y.unop.left) x.1, by
    let T := Opposite.op Y.unop.left
    change c.app T (b.app T ((pullback.snd a b).app T x.1)) = _
    have hbase : a.app T ((pullback.fst a b).app T x.1) =
        b.app T ((pullback.snd a b).app T x.1) := by
      simpa [Functor.comp_apply] using
        congrArg (fun q => q.app T x.1) (pullback.condition (f := a) (g := b))
    have hfst : c.app T (a.app T ((pullback.fst a b).app T x.1)) =
        E.map Y.unop.hom.op y := by
      simpa [Functor.comp_apply] using x.2
    exact (congrArg (c.app T) hbase.symm).trans hfst⟩
  naturality := by
    intro Y Z φ
    ext x
    simp [sectionFiber]

/-- At each object, the section fibres of the two projections and of the two base
transformations form a cartesian square. -/
private theorem sectionFiberPullbackSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) (c : G ⟶ E)
    (X : BigFppfOver B S hS) (y : E.obj (Opposite.op X))
    (Y : (Over X)ᵒᵖ) :
    IsPullback
      (sectionFiberPrecomp B S hS (pullback.fst a b) (a ≫ c) X y |>.app Y)
      (sectionFiberPullbackRight B S hS a b c X y |>.app Y)
      (sectionFiberPrecomp B S hS a c X y |>.app Y)
      (sectionFiberPrecomp B S hS b c X y |>.app Y) := by
  let T := Opposite.op Y.unop.left
  have hbase := ((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type v)).obj T).map_isPullback
    (IsPullback.of_hasPullback a b)
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact Subtype.ext (congrArg (fun q => q.app T x.1) (pullback.condition (f := a) (g := b)))
  · intro x z h
    apply Subtype.ext
    apply Types.ext_of_isPullback hbase
    · simpa [sectionFiberPrecomp] using congrArg Subtype.val h.1
    · simpa [sectionFiberPullbackRight] using congrArg Subtype.val h.2
  · intro x z h
    have heq : a.app T x.1 = b.app T z.1 := by
      simpa [sectionFiberPrecomp] using congrArg Subtype.val h
    obtain ⟨p, hpF, hpH⟩ := Types.exists_of_isPullback hbase x.1 z.1 heq
    have hpF' : (pullback.fst a b).app T p = x.1 := by simpa using hpF
    have hpH' : (pullback.snd a b).app T p = z.1 := by simpa using hpH
    refine ⟨⟨p, ?_⟩, Subtype.ext hpF', Subtype.ext hpH'⟩
    show c.app T (a.app T ((pullback.fst a b).app T p)) = E.map Y.unop.hom.op y
    rw [hpF']
    exact x.2

/-- Relative limit preservation is stable under a fibre product of presheaves
over a common intermediate presheaf. -/
@[stacks 0GDZ]
public theorem relativelyLimitPreserving_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) (c : G ⟶ E)
    (hc : RelativelyLimitPreserving.{u, v, w, w'} B S hS c)
    (hca : RelativelyLimitPreserving.{u, v, w, w'} B S hS (a ≫ c))
    (hcb : RelativelyLimitPreserving.{u, v, w, w'} B S hS (b ≫ c)) :
    RelativelyLimitPreserving.{u, v, w, w'} B S hS
      (pullback.fst a b ≫ a ≫ c) := by
  intro X y I _ _ D cc hlimit haff hpt
  let P := sectionFiber B S hS (pullback.fst a b ≫ a ≫ c) X y
  let F' := sectionFiber B S hS (a ≫ c) X y
  let G' := sectionFiber B S hS c X y
  let H' := sectionFiber B S hS (b ≫ c) X y
  let pF := sectionFiberPrecomp B S hS (pullback.fst a b) (a ≫ c) X y
  let pH := sectionFiberPullbackRight B S hS a b c X y
  let α := sectionFiberPrecomp B S hS a c X y
  let β := sectionFiberPrecomp B S hS b c X y
  let cP := P.mapCocone cc.op
  let cF := F'.mapCocone cc.op
  let cG := G'.mapCocone cc.op
  let cH := H'.mapCocone cc.op
  obtain ⟨hF⟩ := hca X y I D cc hlimit haff hpt
  obtain ⟨hG⟩ := hc X y I D cc hlimit haff hpt
  obtain ⟨hH⟩ := hcb X y I D cc hlimit haff hpt
  exact filteredColimitOfPullbackSquares (Functor.whiskerLeft D.op pF)
    (Functor.whiskerLeft D.op pH) (Functor.whiskerLeft D.op α) (Functor.whiskerLeft D.op β)
    (qF := pF.app (Opposite.op cc.pt)) (qH := pH.app (Opposite.op cc.pt))
    (f₀ := α.app (Opposite.op cc.pt)) (g₀ := β.app (Opposite.op cc.pt))
    (cP := cP) (cF := cF) (cG := cG) (cH := cH)
    hF hG hH
    (fun i => sectionFiberPullbackSquare B S hS a b c X y (Opposite.op (D.obj i.unop)))
    (sectionFiberPullbackSquare B S hS a b c X y (Opposite.op cc.pt))
    (fun i => (pF.naturality (cc.π.app i.unop).op).symm)
    (fun i => (pH.naturality (cc.π.app i.unop).op).symm)
    (fun i => (α.naturality (cc.π.app i.unop).op).symm)
    (fun i => (β.naturality (cc.π.app i.unop).op).symm)

end AlgebraicGeometry
