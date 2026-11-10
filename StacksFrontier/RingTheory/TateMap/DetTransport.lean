module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantEquivIso
public import StacksFrontier.RingTheory.TateMap.DetNL
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget

/-!
# Transport of determinants between two-term presentations

A perfect object `K` of `D(R)` of Tor-amplitude in `[-1, 0]` may be presented by several
two-term complexes of finite projective modules, and the determinant functor identifies `det(K)`
with the determinant line of each. This file computes how two such identifications differ when
the presentations are cochain models of two-term complexes `T`, `T'` related by a chain map
`φ : T → T'` compatible with the identifications: along a degreewise-surjective
quasi-isomorphism they differ by the determinant equivalence of Stacks 0FJJ, and in general by
`det(q) ∘ det(p)⁻¹` for any degreewise-surjective span `T ← W → T'` of `φ`, one of which is
`T ⊕ (T'₁ = T'₁)`.

## Main definitions

* `Stacks.TateMap.toHom`: a chain map of two-term complexes as a morphism of two-term complexes.
* `Stacks.TateMap.coneLine`: the determinant line of the cochain model of a two-term complex is
  its determinant line.
* `Stacks.TateMap.spanTwoTerm`, `Stacks.TateMap.spanP`, `Stacks.TateMap.spanQ`: the
  degreewise-surjective span of a chain map.

## Main results

* `Stacks.TateMap.coneLine_detPresentationIso`: transport along a degreewise-surjective
  quasi-isomorphism.
* `Stacks.TateMap.coneLine_detPresentationIso_span`: transport along a span.
* `Stacks.TateMap.TwoTermHomotopy`: homotopies of chain maps of two-term complexes are an
  equivalence relation compatible with composition, and preserve quasi-isomorphisms.

## References

* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
* [Stacks Project, Lemma 15.87.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.TateMap

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-! ### Chain maps of two-term complexes as morphisms of two-term complexes -/

/-- A chain map of two-term complexes, as a morphism of two-term complexes in the sense of the
determinant line. -/
def toHom {T T' : NaiveCotangent.TwoTerm.{u, u, u} R} (f : NaiveCotangent.ChainMap T T') :
    TwoTermComplex.Hom T.d T'.d :=
  ⟨f.f₁, f.f₀, f.comm.symm⟩

/-- A quasi-isomorphism of two-term complexes is a quasi-isomorphism as a morphism of two-term
complexes. -/
theorem toHom_isQuasiIso {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    {f : NaiveCotangent.ChainMap T T'} (hf : NaiveCotangent.IsQuasiIso f) :
    (toHom f).IsQuasiIso :=
  ⟨hf.1, hf.2⟩

/-- The cochain model of a composite of chain maps is the composite of the cochain models. -/
theorem coneMap_comp {T T' T'' : NaiveCotangent.TwoTerm.{u, u, u} R}
    (g : NaiveCotangent.ChainMap T' T'') (f : NaiveCotangent.ChainMap T T') :
    coneMap (g.comp f) = coneMap f ≫ coneMap g := by
  rw [coneMap, coneMap, coneMap, ← CochainComplex.mappingCone.map_comp]
  congr 1 <;> rw [← Functor.map_comp] <;> rfl

/-- The degree `-1` component of the cochain model of a chain map is the degree `1` component of
the chain map. -/
theorem coneMap_f_negOne {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    (f : NaiveCotangent.ChainMap T T') :
    (coneMap f).f (-1) = (coneNegOneIso T).inv ≫ ModuleCat.ofHom f.f₁ ≫ (coneNegOneIso T').hom := by
  rw [← coneNegOneIso_hom_coneMap_f, Iso.inv_hom_id_assoc]

/-- The degree `0` component of the cochain model of a chain map is the degree `0` component of
the chain map. -/
theorem coneMap_f_zero {T T' : NaiveCotangent.TwoTerm.{u, u, u} R}
    (f : NaiveCotangent.ChainMap T T') :
    (coneMap f).f 0 = (coneZeroIso T).inv ≫ ModuleCat.ofHom f.f₀ ≫ (coneZeroIso T').hom := by
  rw [← coneZeroIso_hom_coneMap_f, Iso.inv_hom_id_assoc]

/-- The identification of the determinant line of the cochain model of a two-term complex with
its determinant line. -/
def coneLine (T : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀] :
    TwoTermComplex.determinantLine ((cone T).d (-1) 0).hom ≃ₗ[R]
      TwoTermComplex.determinantLine T.d :=
  TwoTermComplex.lineCongr _ _ (coneNegOneIso T).symm.toLinearEquiv
    (coneZeroIso T).symm.toLinearEquiv

/-- **Transport between two cochain-model presentations along a degreewise-surjective
quasi-isomorphism.** If two two-term complexes present the same perfect object through
identifications intertwined by a degreewise-surjective quasi-isomorphism `f`, then the two
identifications of the determinant differ by the determinant equivalence of `f`. -/
theorem coneLine_detPresentationIso (K : TwoTermDeterminant.PerfectTwoTermComplex R)
    (T T' : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀]
    [Module.Finite R T'.X₁] [Module.Projective R T'.X₁]
    [Module.Finite R T'.X₀] [Module.Projective R T'.X₀]
    (e : K.obj ≅ DerivedCategory.Q.obj (cone T)) (e' : K.obj ≅ DerivedCategory.Q.obj (cone T'))
    (f : NaiveCotangent.ChainMap T T') (hs : (toHom f).IsDegreewiseSurjective)
    (hq : (toHom f).IsQuasiIso) (hf : e.hom ≫ DerivedCategory.Q.map (coneMap f) = e'.hom)
    (x : ((TwoTermDeterminant.det R).obj ⟨K⟩).of.obj) :
    coneLine T' (TwoTermDeterminant.detPresentationIso K (conePresentation T' e') x) =
      TwoTermComplex.detEquiv (toHom f) hs hq
        (coneLine T (TwoTermDeterminant.detPresentationIso K (conePresentation T e) x)) := by
  let Pp := conePresentation T e
  let Pp' := conePresentation T' e'
  let a := Pp.hom Pp' (coneMap f)
  have := Pp.finite (-1)
  have := Pp.projective (-1)
  have := Pp.finite 0
  have := Pp.projective 0
  have := Pp'.finite (-1)
  have := Pp'.projective (-1)
  have := Pp'.finite 0
  have := Pp'.projective 0
  have h₁ : a.neg = (coneNegOneIso T').toLinearEquiv.toLinearMap ∘ₗ (toHom f).neg ∘ₗ
      (coneNegOneIso T).symm.toLinearEquiv.toLinearMap := by
    change ((coneMap f).f (-1)).hom = _
    rw [coneMap_f_negOne]
    rfl
  have h₀ : a.zero = (coneZeroIso T').toLinearEquiv.toLinearMap ∘ₗ (toHom f).zero ∘ₗ
      (coneZeroIso T).symm.toLinearEquiv.toLinearMap := by
    change ((coneMap f).f 0).hom = _
    rw [coneMap_f_zero]
    rfl
  have hα : T.d ∘ₗ (coneNegOneIso T).symm.toLinearEquiv.toLinearMap =
      (coneZeroIso T).symm.toLinearEquiv.toLinearMap ∘ₗ ((cone T).d (-1) 0).hom :=
    cone_d_comm T
  have hβ : ((cone T').d (-1) 0).hom ∘ₗ (coneNegOneIso T').toLinearEquiv.toLinearMap =
      (coneZeroIso T').toLinearEquiv.toLinearMap ∘ₗ T'.d := by
    ext y
    exact cone_d_coneNegOneIso_hom T' y
  have hs' : a.IsDegreewiseSurjective :=
    TwoTermComplex.isDegreewiseSurjective_conj (toHom f) hs _ _ _ _ a h₁ h₀
  have hq' : a.IsQuasiIso :=
    TwoTermComplex.isQuasiIso_conj (toHom f) hq _ _ hα _ _ hβ a h₁ h₀
  have key := TwoTermDeterminant.detPresentationIso_det_map K K Pp Pp' (𝟙 _) (coneMap f)
    (by
      change e.hom ≫ DerivedCategory.Q.map (coneMap f) ≫ e'.inv = 𝟙 _
      rw [← Category.assoc, hf, Iso.hom_inv_id]) hs' hq' x
  rw [CategoryTheory.Functor.map_id] at key
  change TwoTermDeterminant.detPresentationIso K Pp' x =
    TwoTermComplex.detEquiv a hs' hq' (TwoTermDeterminant.detPresentationIso K Pp x) at key
  rw [key]
  have hc := TwoTermComplex.detEquiv_conj (toHom f) hs hq _ _ hα _ _ hβ a h₁ h₀ hs' hq'
  refine (congrArg (coneLine T') (LinearEquiv.congr_fun hc _)).trans ?_
  have hr : ∀ {M N : ModuleCat R} (i : M ≅ N),
      i.toLinearEquiv.trans i.symm.toLinearEquiv = LinearEquiv.refl R _ := fun i => by
    ext y
    exact i.hom_inv_id_apply y
  have hl := TwoTermComplex.lineCongr_trans T'.d ((cone T').d (-1) 0).hom T'.d
    (coneNegOneIso T').toLinearEquiv (coneZeroIso T').toLinearEquiv
    (coneNegOneIso T').symm.toLinearEquiv (coneZeroIso T').symm.toLinearEquiv
  rw [hr, hr, TwoTermComplex.lineCongr_refl] at hl
  exact LinearEquiv.congr_fun hl _

/-! ### Homotopies of chain maps of two-term complexes -/

namespace TwoTermHomotopy

open NaiveCotangent

variable {S : Type*} [CommRing S] {X Y Z : TwoTerm S}

/-- Every chain map is homotopic to itself. -/
theorem refl (f : ChainMap X Y) : Homotopic f f := ⟨0, by simp, by simp⟩

/-- Homotopy of chain maps is symmetric. -/
theorem symm {f g : ChainMap X Y} (h : Homotopic f g) : Homotopic g f := by
  obtain ⟨k, h₁, h₀⟩ := h
  refine ⟨-k, ?_, ?_⟩
  · rw [← neg_sub, h₁, LinearMap.neg_comp]
  · rw [← neg_sub, h₀, LinearMap.comp_neg]

/-- Homotopy of chain maps is transitive. -/
theorem trans {f g k : ChainMap X Y} (h : Homotopic f g) (h' : Homotopic g k) :
    Homotopic f k := by
  obtain ⟨a, a₁, a₀⟩ := h
  obtain ⟨b, b₁, b₀⟩ := h'
  refine ⟨a + b, ?_, ?_⟩
  · rw [LinearMap.add_comp, ← a₁, ← b₁, sub_add_sub_cancel]
  · rw [LinearMap.comp_add, ← a₀, ← b₀, sub_add_sub_cancel]

/-- Homotopic chain maps stay homotopic after composing with a chain map on the left. -/
theorem comp_left {f g : ChainMap X Y} (h : Homotopic f g) (k : ChainMap Y Z) :
    Homotopic (k.comp f) (k.comp g) := by
  obtain ⟨a, a₁, a₀⟩ := h
  refine ⟨k.f₁ ∘ₗ a, ?_, ?_⟩
  · change k.f₁ ∘ₗ f.f₁ - k.f₁ ∘ₗ g.f₁ = _
    rw [← LinearMap.comp_sub, a₁, LinearMap.comp_assoc]
  · change k.f₀ ∘ₗ f.f₀ - k.f₀ ∘ₗ g.f₀ = _
    rw [← LinearMap.comp_sub, a₀, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, k.comm]

/-- Homotopic chain maps stay homotopic after composing with a chain map on the right. -/
theorem comp_right {f g : ChainMap Y Z} (h : Homotopic f g) (k : ChainMap X Y) :
    Homotopic (f.comp k) (g.comp k) := by
  obtain ⟨a, a₁, a₀⟩ := h
  refine ⟨a ∘ₗ k.f₀, ?_, ?_⟩
  · change f.f₁ ∘ₗ k.f₁ - g.f₁ ∘ₗ k.f₁ = _
    rw [← LinearMap.sub_comp, a₁, LinearMap.comp_assoc, LinearMap.comp_assoc, ← k.comm]
  · change f.f₀ ∘ₗ k.f₀ - g.f₀ ∘ₗ k.f₀ = _
    rw [← LinearMap.sub_comp, a₀, LinearMap.comp_assoc]

/-- Homotopic chain maps are quasi-isomorphisms together. -/
theorem isQuasiIso {f g : ChainMap X Y} (h : Homotopic f g) (hf : IsQuasiIso f) :
    IsQuasiIso g := by
  refine ⟨?_, ?_⟩
  · rw [← ChainMap.onH₁_eq_of_homotopic h]
    exact hf.1
  · rw [← ChainMap.onH₀_eq_of_homotopic h]
    exact hf.2

/-- A composite of quasi-isomorphisms is a quasi-isomorphism. -/
theorem isQuasiIso_comp {f : ChainMap X Y} {g : ChainMap Y Z} (hf : IsQuasiIso f)
    (hg : IsQuasiIso g) : IsQuasiIso (g.comp f) := IsQuasiIso.comp hg hf

/-- If `g` and `g ∘ f` are quasi-isomorphisms, then so is `f`. -/
theorem isQuasiIso_of_comp {f : ChainMap X Y} {g : ChainMap Y Z} (hg : IsQuasiIso g)
    (hgf : IsQuasiIso (g.comp f)) : IsQuasiIso f := by
  refine ⟨?_, ?_⟩
  · refine (Function.Bijective.of_comp_iff' hg.1 f.onH₁).mp ?_
    rw [show (g.onH₁ ∘ f.onH₁ : H₁ X → H₁ Z) = (g.comp f).onH₁ from
      congrArg (fun m : H₁ X →ₗ[S] H₁ Z => (m : H₁ X → H₁ Z)) (ChainMap.onH₁_comp g f).symm]
    exact hgf.1
  · refine (Function.Bijective.of_comp_iff' hg.2 f.onH₀).mp ?_
    rw [show (g.onH₀ ∘ f.onH₀ : H₀ X → H₀ Z) = (g.comp f).onH₀ from
      congrArg (fun m : H₀ X →ₗ[S] H₀ Z => (m : H₀ X → H₀ Z)) (ChainMap.onH₀_comp g f).symm]
    exact hgf.2

end TwoTermHomotopy

/-! ### A degreewise-surjective span of a quasi-isomorphism -/

section Span

open NaiveCotangent

variable {S : Type u} [CommRing S] (T T' : TwoTerm.{u, u, u} S)

/-- The two-term complex `T ⊕ (T'₁ = T'₁)`, the source of a degreewise-surjective span of a
chain map `T → T'`. -/
abbrev spanTwoTerm : TwoTerm.{u, u, u} S where
  X₁ := T.X₁ × T'.X₁
  X₀ := T.X₀ × T'.X₁
  d := T.d.prodMap LinearMap.id

/-- The projection of the span onto `T`. -/
def spanP : ChainMap (spanTwoTerm T T') T where
  f₁ := LinearMap.fst _ _ _
  f₀ := LinearMap.fst _ _ _
  comm := LinearMap.ext fun _ => rfl

variable {T T'}

/-- The second leg of the span of a chain map `φ : T → T'`. -/
def spanQ (φ : ChainMap T T') : ChainMap (spanTwoTerm T T') T' where
  f₁ := φ.f₁ ∘ₗ LinearMap.fst _ _ _ + LinearMap.snd _ _ _
  f₀ := φ.f₀ ∘ₗ LinearMap.fst _ _ _ + T'.d ∘ₗ LinearMap.snd _ _ _
  comm := by
    refine LinearMap.ext fun ⟨x, y⟩ => ?_
    have := LinearMap.congr_fun φ.comm x
    simp only [LinearMap.comp_apply] at this
    simp [spanTwoTerm, this]

variable (T T')

/-- The inclusion of `T` into the span. -/
def spanI : ChainMap T (spanTwoTerm T T') where
  f₁ := LinearMap.inl _ _ _
  f₀ := LinearMap.inl _ _ _
  comm := LinearMap.ext fun x => by simp [spanTwoTerm]

/-- The projection of the span onto `T` is a homotopy equivalence, with homotopy inverse the
inclusion `Stacks.TateMap.spanI`. -/
theorem isHomotopyEquiv_spanP : IsHomotopyEquiv (spanP T T') := by
  refine ⟨spanI T T', ⟨-(LinearMap.inr _ _ _ ∘ₗ LinearMap.snd _ _ _), ?_, ?_⟩, ⟨0, ?_, ?_⟩⟩
  all_goals refine LinearMap.ext fun x => ?_
  all_goals simp [spanTwoTerm, spanP, spanI, ChainMap.comp, ChainMap.id, Prod.ext_iff]

/-- The projection of the span onto `T` is degreewise surjective. -/
theorem spanP_surjective : (toHom (spanP T T')).IsDegreewiseSurjective :=
  ⟨LinearMap.fst_surjective, LinearMap.fst_surjective⟩

/-- The projection of the span onto `T` is a quasi-isomorphism. -/
theorem isQuasiIso_spanP : IsQuasiIso (spanP T T') :=
  isQuasiIso_of_isHomotopyEquiv (isHomotopyEquiv_spanP T T')

variable {T T'}

/-- The second leg of the span of `φ` is homotopic to `φ` composed with the projection onto `T`. -/
theorem homotopic_spanQ (φ : ChainMap T T') : Homotopic (spanQ φ) (φ.comp (spanP T T')) := by
  refine ⟨LinearMap.snd _ _ _, ?_, ?_⟩
  all_goals refine LinearMap.ext fun x => ?_
  all_goals simp [spanQ, spanP, ChainMap.comp]

/-- The second leg of the span of a quasi-isomorphism is a quasi-isomorphism. -/
theorem isQuasiIso_spanQ {φ : ChainMap T T'} (hφ : IsQuasiIso φ) : IsQuasiIso (spanQ φ) :=
  TwoTermHomotopy.isQuasiIso (TwoTermHomotopy.symm (homotopic_spanQ φ))
    (TwoTermHomotopy.isQuasiIso_comp (isQuasiIso_spanP T T') hφ)

/-- The second leg of the span of a quasi-isomorphism is degreewise surjective. -/
theorem spanQ_surjective {φ : ChainMap T T'} (hφ : IsQuasiIso φ) :
    (toHom (spanQ φ)).IsDegreewiseSurjective := by
  refine ⟨fun y ↦ ⟨(0, y), by simp [toHom, spanQ]⟩, fun z ↦ ?_⟩
  obtain ⟨m, w, h⟩ := NaiveCotangent.exists_add_d_of_surjective_onH₀ φ hφ.2.2 z
  exact ⟨(m, w), by simpa [toHom, spanQ] using h⟩

end Span

/-! ### Finiteness of base changed two-term complexes -/

section BaseChangeInstances

variable {S : Type*} [CommRing S] (S' : Type*) [CommRing S'] [Algebra S S']
  (T : NaiveCotangent.TwoTerm S)

/-- The degree `1` term of a base change of a finite two-term complex is finite. -/
instance [Module.Finite S T.X₁] : Module.Finite S' (T.baseChange S').X₁ :=
  inferInstanceAs (Module.Finite S' (S' ⊗[S] T.X₁))

/-- The degree `1` term of a base change of a projective two-term complex is projective. -/
instance [Module.Projective S T.X₁] : Module.Projective S' (T.baseChange S').X₁ :=
  inferInstanceAs (Module.Projective S' (S' ⊗[S] T.X₁))

/-- The degree `0` term of a base change of a finite two-term complex is finite. -/
instance [Module.Finite S T.X₀] : Module.Finite S' (T.baseChange S').X₀ :=
  inferInstanceAs (Module.Finite S' (S' ⊗[S] T.X₀))

/-- The degree `0` term of a base change of a projective two-term complex is projective. -/
instance [Module.Projective S T.X₀] : Module.Projective S' (T.baseChange S').X₀ :=
  inferInstanceAs (Module.Projective S' (S' ⊗[S] T.X₀))

end BaseChangeInstances

/-! ### Transport along a span -/

/-- **Transport between two cochain-model presentations along a quasi-isomorphism**, computed
on any degreewise-surjective span `T ← W → T'` of it: the two identifications of the
determinant differ by `det(q) ∘ det(p)⁻¹`. -/
theorem coneLine_detPresentationIso_span (K : TwoTermDeterminant.PerfectTwoTermComplex R)
    (T T' W : NaiveCotangent.TwoTerm.{u, u, u} R)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₀] [Module.Projective R T.X₀]
    [Module.Finite R T'.X₁] [Module.Projective R T'.X₁]
    [Module.Finite R T'.X₀] [Module.Projective R T'.X₀]
    [Module.Finite R W.X₁] [Module.Projective R W.X₁]
    [Module.Finite R W.X₀] [Module.Projective R W.X₀]
    (e : K.obj ≅ DerivedCategory.Q.obj (cone T)) (e' : K.obj ≅ DerivedCategory.Q.obj (cone T'))
    (φ : NaiveCotangent.ChainMap T T') (hf : e.hom ≫ DerivedCategory.Q.map (coneMap φ) = e'.hom)
    (p : NaiveCotangent.ChainMap W T) (q : NaiveCotangent.ChainMap W T')
    (hps : (toHom p).IsDegreewiseSurjective) (hpq : NaiveCotangent.IsQuasiIso p)
    (hqs : (toHom q).IsDegreewiseSurjective) (hqq : NaiveCotangent.IsQuasiIso q)
    (hh : NaiveCotangent.Homotopic q (φ.comp p))
    (x : ((TwoTermDeterminant.det R).obj ⟨K⟩).of.obj) :
    coneLine T' (TwoTermDeterminant.detPresentationIso K (conePresentation T' e') x) =
      TwoTermComplex.detEquiv (toHom q) hqs (toHom_isQuasiIso hqq)
        ((TwoTermComplex.detEquiv (toHom p) hps (toHom_isQuasiIso hpq)).symm
          (coneLine T (TwoTermDeterminant.detPresentationIso K (conePresentation T e) x))) := by
  have : IsIso (DerivedCategory.Q.map (coneMap p)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coneMap hpq)
  let eW : K.obj ≅ DerivedCategory.Q.obj (cone W) :=
    e ≪≫ (asIso (DerivedCategory.Q.map (coneMap p))).symm
  have h1 := coneLine_detPresentationIso K W T eW e p hps (toHom_isQuasiIso hpq)
    (by simp [eW]) x
  have h2 := coneLine_detPresentationIso K W T' eW e' q hqs (toHom_isQuasiIso hqq)
    (by
      rw [Q_map_coneMap_eq_of_homotopic hh, coneMap_comp, Functor.map_comp]
      simp [eW, hf]) x
  rw [h2, h1, LinearEquiv.symm_apply_apply]

end Stacks.TateMap
