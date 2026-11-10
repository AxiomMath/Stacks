module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SheafCoproduct

/-!
# A coproduct of sheaves of sets is stable under base change

Let `G` be the coproduct of a family of sheaves of sets `Fᵢ` on a site and let `Y ⟶ G` be
any morphism of sheaves. Then `Y` is the coproduct of the fibre products `Fᵢ ×_G Y`. This
file proves that, in the cofan formulation: a family of pullback squares over the summands
of a coproduct cofan assembles into a coproduct cofan over the base.

## Main results

* `AlgebraicGeometry.Space.pullback_coproduct_isColimit` is the statement above.
* `AlgebraicGeometry.Space.cofan_isColimit_of_local_lifts` recognizes a cofan of sheaves as a
  colimit from a local lifting property and a compatibility property, and is where the sheaf
  condition is used.

## Implementation notes

Descent for the universal property is done by hand on sections rather than by a general
colimit comparison: the descent datum glueing the local lifts is a family of elements for a
covering sieve, so `CategoryTheory.Presieve.IsSheafFor` supplies both the amalgamation and
its uniqueness. The compatibility of two local lifts over different indices uses that the
site's sheaves of sets form a finitary extensive category, so two distinct summands of a
coproduct are disjoint; that is where the sheafification hypothesis enters.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- Two sections of a sheaf of sets agree as soon as they agree after restriction along
every arrow of a covering sieve. -/
lemma sheaf_sections_ext
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (Z : Sheaf J (Type u)) {T : C} {R : Sieve T} (hR : R ∈ J T)
    (x y : Z.obj.obj (Opposite.op T))
    (h : ∀ ⦃V : C⦄ (a : V ⟶ T), R a → Z.obj.map a.op x = Z.obj.map a.op y) :
    x = y :=
  (Z.property.isSheafFor R hR).isSeparatedFor.ext (fun _ a ha => h a ha)

/-- Local lifts of a section of `Y` through the members of a cofan over `Y`, compatible in
the sense that any two of them already agree in the vertex of the cofan, glue to a section
of that vertex. -/
lemma exists_section_of_local_lifts
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {I : Type v} {H : I → Sheaf J (Type u)} {Y : Sheaf J (Type u)}
    (p : ∀ i, H i ⟶ Y) (c : Cofan H)
    (hcompat : ∀ {T : C} (i j : I) (x : (H i).obj.obj (Opposite.op T))
      (y : (H j).obj.obj (Opposite.op T)),
      (p i).hom.app (Opposite.op T) x = (p j).hom.app (Opposite.op T) y →
      (c.inj i).hom.app (Opposite.op T) x = (c.inj j).hom.app (Opposite.op T) y)
    {T : C} (y : Y.obj.obj (Opposite.op T))
    (hlocal : ∃ R : Sieve T, R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
      ∃ (i : I) (z : (H i).obj.obj (Opposite.op V)),
        (p i).hom.app (Opposite.op V) z = Y.obj.map a.op y) :
    ∃ z : c.pt.obj.obj (Opposite.op T), ∀ ⦃V : C⦄ (a : V ⟶ T) (i : I)
      (x : (H i).obj.obj (Opposite.op V)),
      (p i).hom.app (Opposite.op V) x = Y.obj.map a.op y →
      c.pt.obj.map a.op z = (c.inj i).hom.app (Opposite.op V) x := by
  obtain ⟨R, hR, hr⟩ := hlocal
  choose idx lift hlift using @hr
  let fam : Presieve.FamilyOfElements c.pt.obj R.arrows :=
    fun V a ha => (c.inj (idx a ha)).hom.app (Opposite.op V) (lift a ha)
  have hfam : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W a b ha
    change (c.inj _).hom.app _ (lift (b ≫ a) _) =
      c.pt.obj.map b.op ((c.inj _).hom.app _ (lift a ha))
    rw [← NatTrans.naturality_apply]
    apply hcompat
    rw [hlift, NatTrans.naturality_apply, hlift, ← Functor.map_comp_apply]
    rfl
  obtain ⟨z, hz, _⟩ := (c.pt.property.isSheafFor R hR) fam hfam
  refine ⟨z, fun V a i x hx => sheaf_sections_ext c.pt (J.pullback_stable a hR) _ _
    fun W b hb => ?_⟩
  change R (b ≫ a) at hb
  rw [← Functor.map_comp_apply]
  change c.pt.obj.map (b ≫ a).op z =
    c.pt.obj.map b.op ((c.inj i).hom.app _ x)
  rw [hz (b ≫ a) hb, ← NatTrans.naturality_apply]
  apply hcompat
  rw [hlift, NatTrans.naturality_apply, hx, ← Functor.map_comp_apply]
  rfl

/-- A cofan of sheaves of sets whose legs lift every section of the vertex locally, and
whose lifts are pairwise compatible in any cofan, is a colimit. -/
noncomputable def cofan_isColimit_of_local_lifts
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {I : Type v} {H : I → Sheaf J (Type u)} {Y : Sheaf J (Type u)}
    (p : ∀ i, H i ⟶ Y)
    (hlocal : ∀ {T : C} (y : Y.obj.obj (Opposite.op T)),
      ∃ R : Sieve T, R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
        ∃ (i : I) (z : (H i).obj.obj (Opposite.op V)),
          (p i).hom.app (Opposite.op V) z = Y.obj.map a.op y)
    (hcompat : ∀ (c : Cofan H) {T : C} (i j : I)
      (x : (H i).obj.obj (Opposite.op T)) (y : (H j).obj.obj (Opposite.op T)),
      (p i).hom.app (Opposite.op T) x = (p j).hom.app (Opposite.op T) y →
      (c.inj i).hom.app (Opposite.op T) x = (c.inj j).hom.app (Opposite.op T) y) :
    IsColimit (Cofan.mk Y p) := by
  have uniq (c : Cofan H) {T : C} (y : Y.obj.obj (Opposite.op T))
      (z z' : c.pt.obj.obj (Opposite.op T))
      (hz : ∀ ⦃V : C⦄ (a : V ⟶ T) (i : I) (x : (H i).obj.obj (Opposite.op V)),
        (p i).hom.app (Opposite.op V) x = Y.obj.map a.op y →
        c.pt.obj.map a.op z = (c.inj i).hom.app (Opposite.op V) x)
      (hz' : ∀ ⦃V : C⦄ (a : V ⟶ T) (i : I) (x : (H i).obj.obj (Opposite.op V)),
        (p i).hom.app (Opposite.op V) x = Y.obj.map a.op y →
        c.pt.obj.map a.op z' = (c.inj i).hom.app (Opposite.op V) x) : z = z' := by
    obtain ⟨R, hR, hr⟩ := hlocal y
    refine sheaf_sections_ext c.pt hR _ _ fun V a ha => ?_
    obtain ⟨i, x, hx⟩ := hr a ha
    rw [hz a i x hx, hz' a i x hx]
  choose d hd using fun (c : Cofan H) (T : C) (y : Y.obj.obj (Opposite.op T)) =>
    exists_section_of_local_lifts p c (hcompat c) y (hlocal y)
  let desc (c : Cofan H) : Y ⟶ c.pt := ⟨{
    app := fun T => ↾(d c T.unop)
    naturality := by
      intro T V a
      ext y
      change d c V.unop (Y.obj.map a y) = c.pt.obj.map a (d c T.unop y)
      refine uniq c (Y.obj.map a y) _ _ (hd c V.unop _) fun W b i x hx => ?_
      rw [← Functor.map_comp_apply]
      exact hd c T.unop y (b ≫ a.unop) i x (by
        simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] using hx) }⟩
  refine Cofan.IsColimit.mk (Cofan.mk Y p) desc ?_ ?_
  · intro c i
    ext T x
    change d c T.unop ((p i).hom.app T x) = (c.inj i).hom.app T x
    simpa using hd c T.unop ((p i).hom.app T x) (𝟙 T.unop) i x (by simp)
  · intro c m hm
    ext T y
    refine uniq c y _ _ (fun V a i x hx => ?_) (hd c T.unop y)
    change c.pt.obj.map a.op (m.hom.app T y) = _
    rw [← NatTrans.naturality_apply]
    change m.hom.app _ (Y.obj.map a.op y) = _
    rw [← hx]
    exact congrArg (fun n : H i ⟶ c.pt => n.hom.app _ x) (hm i)

/-- Two sections of the pullbacks of a coproduct cofan which agree over the base already
agree in any cofan over the pullbacks: distinct summands of a coproduct of sheaves of sets
are disjoint. -/
lemma pullback_coproduct_compatible
    {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J (Type u)] [J.Subcanonical]
    {I : Type v} {Fi : I → Sheaf J (Type u)} {G Y : Sheaf J (Type u)}
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) (f : Y ⟶ G)
    {H : I → Sheaf J (Type u)} (p : ∀ i, H i ⟶ Y) (q : ∀ i, H i ⟶ Fi i)
    (hP : ∀ i, IsPullback (p i) (q i) f (ι i)) (c : Cofan H)
    {T : C} (i j : I) (x : (H i).obj.obj (Opposite.op T))
    (y : (H j).obj.obj (Opposite.op T))
    (hxy : (p i).hom.app (Opposite.op T) x = (p j).hom.app (Opposite.op T) y) :
    (c.inj i).hom.app (Opposite.op T) x = (c.inj j).hom.app (Opposite.op T) y := by
  let a : J.yoneda.obj T ⟶ H i := J.yonedaEquiv.symm x
  let b : J.yoneda.obj T ⟶ H j := J.yonedaEquiv.symm y
  have hab : a ≫ p i = b ≫ p j := by
    simp only [a, b, J.yonedaEquiv_symm_naturality_right, hxy]
  have hbin := splitColimit ι hc i
  by_cases hij : i = j
  · subst j
    have : Mono (ι i) := FinitaryExtensive.mono_inl_of_isColimit hbin
    have : Mono (p i) := (hP i).mono_fst_of_mono
    simpa [a, b] using congrArg ((c.inj i).hom.app (Opposite.op T))
      (congrArg J.yonedaEquiv ((cancel_mono (p i)).mp hab))
  · let O := otherSheaf (J := J) (fun k => (ι k).hom) i
    let k : O ⟶ G := otherInclusion (J := J) (fun k => (ι k).hom) i
    let r : Fi j ⟶ O := otherMap ι i j (Ne.symm hij)
    have hdisj : IsPullback (initial.to (Fi i)) (initial.to O) (ι i) k :=
      FinitaryExtensive.isPullback_initial_to_binaryCofan hbin
    have hw : (a ≫ q i) ≫ ι i = (b ≫ q j ≫ r) ≫ k := by
      simp only [Category.assoc, otherMap_comp_inclusion, r, k]
      rw [← (hP i).w, ← (hP j).w]
      simpa only [← Category.assoc] using congrArg (fun z => z ≫ f) hab
    let l : J.yoneda.obj T ⟶ ⊥_ (Sheaf J (Type u)) :=
      hdisj.lift (a ≫ q i) (b ≫ q j ≫ r) hw
    have hinit : IsInitial (J.yoneda.obj T) := IsInitial.ofStrict l initialIsInitial
    simpa [J.yonedaEquiv_comp, a, b] using
      congrArg J.yonedaEquiv (hinit.hom_ext (a ≫ c.inj i) (b ≫ c.inj j))

/-- A section of the base lifts, locally on a covering sieve, to one of the pullbacks of a
coproduct cofan. -/
lemma pullback_coproduct_locally_factors
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [J.Subcanonical]
    {I : Type v} (Fi : I → Sheaf J (Type u)) (G Y : Sheaf J (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) (f : Y ⟶ G)
    (H : I → Sheaf J (Type u)) (p : ∀ i, H i ⟶ Y) (q : ∀ i, H i ⟶ Fi i)
    (hP : ∀ i, IsPullback (p i) (q i) f (ι i))
    {T : C} (y : Y.obj.obj (Opposite.op T)) :
    ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (a : V ⟶ T), R a →
      ∃ (i : I) (z : (H i).obj.obj (Opposite.op V)),
        (p i).hom.app (Opposite.op V) z = Y.obj.map a.op y := by
  obtain ⟨R, hR, hloc⟩ := coproduct_locally_factors Fi G ι hc
    (f.hom.app (Opposite.op T) y)
  refine ⟨R, hR, fun V a ha => ?_⟩
  obtain ⟨i, x, hx⟩ := hloc a ha
  let α : J.yoneda.obj V ⟶ Y := J.yonedaEquiv.symm (Y.obj.map a.op y)
  let β : J.yoneda.obj V ⟶ Fi i := J.yonedaEquiv.symm x
  have hαβ : α ≫ f = β ≫ ι i := by
    simp only [α, β, J.yonedaEquiv_symm_naturality_right]
    exact congrArg _ ((NatTrans.naturality_apply f.hom _ y).trans hx.symm)
  let ℓ : J.yoneda.obj V ⟶ H i := (hP i).lift α β hαβ
  refine ⟨i, J.yonedaEquiv ℓ, ?_⟩
  have hfac : ℓ ≫ p i = α := (hP i).lift_fst _ _ _
  have hv := congrArg J.yonedaEquiv hfac
  simpa [J.yonedaEquiv_comp, α] using hv

/-- A family of pullback squares over the summands of a coproduct cofan of sheaves of sets
is a coproduct cofan over the base. -/
noncomputable def pullback_coproduct_isColimit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [J.Subcanonical] [HasSheafify J (Type u)]
    {I : Type v} {Fi : I → Sheaf J (Type u)} {G Y : Sheaf J (Type u)}
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι)) (f : Y ⟶ G)
    {H : I → Sheaf J (Type u)} (p : ∀ i, H i ⟶ Y) (q : ∀ i, H i ⟶ Fi i)
    (hP : ∀ i, IsPullback (p i) (q i) f (ι i)) :
    IsColimit (Cofan.mk Y p) :=
  cofan_isColimit_of_local_lifts p
    (fun y => pullback_coproduct_locally_factors Fi G Y ι hc f H p q hP y)
    (fun c _ i j x y hxy => pullback_coproduct_compatible ι hc f p q hP c i j x y hxy)

end AlgebraicGeometry.Space

end
