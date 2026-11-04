module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechTranslation

/-!
# The gluing relations of a Čech covering in `Complexes_{X/Y}`

Let `C : CechCover T I` be a Čech covering in `Complexes_{X/Y}` and `R` a refinement of it indexed
by a type in `Type u`, with disjoint union `V = ∐ W_k` and the object `K_0` of `Complexes_{X/Y}`
over `V` glued from the restrictions of the `K_{σ k}`
(`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.unionComplex`). Every
morphism of `Complexes_{X/Y}` is cartesian, so the gluing isomorphisms of `C` and of `K_0` are
read as relations between morphisms out of one object:

* two morphisms `x : A ⟶ K_i` and `y : A ⟶ K_j` are *related* when they factor through one
  morphism to the double overlap `K_{ij}`
  (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.IsRelated`). By the cocycle condition of
  `C` this is an equivalence relation, and a morphism is related to exactly one morphism over each
  base map;
* a morphism `a : A ⟶ K_0` and a morphism `x : A ⟶ K_i` are *related* when they are on every
  piece of `A` over the members `W_k`
  (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.IsUnionRelated`);
* two morphisms `a, a' : A ⟶ K_0` differ by the *transport* of the gluing isomorphisms when every
  morphism to a member related to the restriction of `a` is related to that of `a'`
  (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.IsUnionTransport`). This
  is the descent datum of `K_0` relative to `V ⟶ T`.

These relations carry the input of Stacks 0DLA for the Čech nerve of `V ⟶ T` and the translation of
its output.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}

/-! ### Lifts and base maps -/

section Generic

variable {x y z : ComplexesObject D}

/-- **Every morphism of `Complexes_{X/Y}` is cartesian**: a morphism `g : z ⟶ x` whose base map
factors as `β ≫ Φ.base` factors through `Φ : y ⟶ x` by a morphism over `β`. -/
theorem exists_complexesHom_lift (Φ : ComplexesHom y x) (β : z.T ⟶ y.T) (g : ComplexesHom z x)
    (hg : β ≫ Φ.base = g.base) : ∃ m : ComplexesHom z y, m.base = β ∧ m.comp Φ = g := by
  obtain ⟨gb, gf, gi⟩ := g
  change β ≫ Φ.base = gb at hg
  subst hg
  exact ⟨liftAlong Φ β (asIso gf), rfl, liftAlong_comp Φ β (asIso gf)⟩

/-- A morphism of `Complexes_{X/Y}` read over an equal base map, through the comparison of the two
derived pullbacks, is the same morphism. -/
theorem complexesHom_mk_trans_eq {Q A : ComplexesObject D} (m : ComplexesHom Q A)
    {β : Q.T ⟶ A.T} (hb : β = m.base) :
    (⟨β, ((D.relativeMapComparison hb).app A.E ≪≫ asIso m.fibre).hom, Iso.isIso_hom _⟩ :
      ComplexesHom Q A) = m := by
  obtain ⟨b, f, i⟩ := m
  change β = b at hb
  subst hb
  refine complexesHom_eq_of_heq rfl (heq_of_eq ?_)
  simp only [Iso.trans_hom, Iso.app_hom, asIso_hom, relativeMapComparison_hom_app, eqToHom_refl,
    Category.id_comp]

/-- A morphism into a fibre product of test schemes, given by its two components. -/
theorem exists_hom_of_isPullback_left {P X Y Z W : SchemesOver D.Y} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hP : IsPullback fst.left snd.left f.left g.left)
    (u : W ⟶ X) (v : W ⟶ Y) (h : u ≫ f = v ≫ g) : ∃ t : W ⟶ P, t ≫ fst = u ∧ t ≫ snd = v := by
  have h' : u.left ≫ f.left = v.left ≫ g.left := by
    simpa only [CostructuredArrow.comp_left] using congrArg CommaMorphism.left h
  refine ⟨CostructuredArrow.homMk (hP.lift u.left v.left h') ?_, ?_, ?_⟩
  · rw [← CostructuredArrow.w fst, ← Category.assoc, ← Functor.map_comp, IsPullback.lift_fst]
    exact CostructuredArrow.w u
  · exact CostructuredArrow.hom_ext _ _ (IsPullback.lift_fst _ _ _ _)
  · exact CostructuredArrow.hom_ext _ _ (IsPullback.lift_snd _ _ _ _)

/-- Two morphisms into a fibre product of test schemes with the same components are equal. -/
theorem hom_ext_of_isPullback_left {P X Y Z W : SchemesOver D.Y} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hP : IsPullback fst.left snd.left f.left g.left) {t t' : W ⟶ P}
    (h₁ : t ≫ fst = t' ≫ fst) (h₂ : t ≫ snd = t' ≫ snd) : t = t' :=
  CostructuredArrow.hom_ext _ _ (hP.hom_ext
    (by simpa only [CostructuredArrow.comp_left] using congrArg CommaMorphism.left h₁)
    (by simpa only [CostructuredArrow.comp_left] using congrArg CommaMorphism.left h₂))

end Generic

namespace CechCover

variable {T : SchemesOver D.Y} {I : Type (u + 1)}

/-! ### Morphisms related through the gluing isomorphisms of a Čech covering -/

section Related

variable (C : CechCover T I)

/-- **Two morphisms to members of a Čech covering are related** when they factor through one
morphism to the double overlap: `x : A ⟶ K_i` and `y : A ⟶ K_j` agree through the gluing
isomorphism `φ_ij`. -/
def IsRelated {A : ComplexesObject D} {i j : I} (x : ComplexesHom A (C.X i))
    (y : ComplexesHom A (C.X j)) : Prop :=
  ∃ o : ComplexesHom A (C.X₂ i j), o.comp (C.n i j) = x ∧ o.comp (C.m i j) = y

variable {C} {A : ComplexesObject D}

/-- Related morphisms have base maps agreeing over `T`. -/
theorem IsRelated.base_w {i j : I} {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)}
    (h : C.IsRelated x y) : x.base ≫ C.a i = y.base ≫ C.a j := by
  obtain ⟨o, rfl, rfl⟩ := h
  show (o.base ≫ (C.n i j).base) ≫ C.a i = (o.base ≫ (C.m i j).base) ≫ C.a j
  rw [Category.assoc, Category.assoc, C.w]

/-- A morphism to a member is related to a morphism over every base map to another member
agreeing over `T`. -/
theorem IsRelated.exists_right {i : I} (x : ComplexesHom A (C.X i)) (j : I)
    (zj : A.T ⟶ (C.X j).T) (h : x.base ≫ C.a i = zj ≫ C.a j) :
    ∃ y : ComplexesHom A (C.X j), y.base = zj ∧ C.IsRelated x y := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_isPullback_left (C.isPullback₂ i j) x.base zj h
  obtain ⟨o, hob, ho⟩ := exists_complexesHom_lift (C.n i j) b x hb₁
  refine ⟨o.comp (C.m i j), ?_, o, ho, rfl⟩
  show o.base ≫ (C.m i j).base = zj
  rw [hob, hb₂]

/-- A morphism to a member is related to a morphism from every base map to another member
agreeing over `T`. -/
theorem IsRelated.exists_left {j : I} (y : ComplexesHom A (C.X j)) (i : I)
    (zi : A.T ⟶ (C.X i).T) (h : zi ≫ C.a i = y.base ≫ C.a j) :
    ∃ x : ComplexesHom A (C.X i), x.base = zi ∧ C.IsRelated x y := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_isPullback_left (C.isPullback₂ i j) zi y.base h
  obtain ⟨o, hob, ho⟩ := exists_complexesHom_lift (C.m i j) b y hb₂
  refine ⟨o.comp (C.n i j), ?_, o, rfl, ho⟩
  show o.base ≫ (C.n i j).base = zi
  rw [hob, hb₁]

/-- A morphism is related to at most one morphism over a given base map. -/
theorem IsRelated.unique {i j : I} {x : ComplexesHom A (C.X i)} {y y' : ComplexesHom A (C.X j)}
    (h : C.IsRelated x y) (h' : C.IsRelated x y') (hb : y.base = y'.base) : y = y' := by
  obtain ⟨o, ho₁, ho₂⟩ := h
  obtain ⟨o', ho₁', ho₂'⟩ := h'
  have e₁ : o.base ≫ (C.n i j).base = o'.base ≫ (C.n i j).base :=
    (congrArg ComplexesHom.base ho₁).trans (congrArg ComplexesHom.base ho₁').symm
  have e₂ : o.base ≫ (C.m i j).base = o'.base ≫ (C.m i j).base :=
    (congrArg ComplexesHom.base ho₂).trans (hb.trans (congrArg ComplexesHom.base ho₂').symm)
  have e : o = o' := complexesHom_cancel_right (C.n i j)
    (hom_ext_of_isPullback_left (C.isPullback₂ i j) e₁ e₂) (ho₁.trans ho₁'.symm)
  subst e
  exact ho₂.symm.trans ho₂'

/-- **The cocycle condition**: the relation is transitive, through the triple overlaps. -/
theorem IsRelated.trans {i j k : I} {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)}
    {w : ComplexesHom A (C.X k)} (h : C.IsRelated x y) (h' : C.IsRelated y w) :
    C.IsRelated x w := by
  obtain ⟨o₁, h₁, h₂⟩ := h
  obtain ⟨o₂, h₂', h₃⟩ := h'
  have e : o₁.base ≫ (C.m i j).base = o₂.base ≫ (C.n j k).base :=
    (congrArg ComplexesHom.base h₂).trans (congrArg ComplexesHom.base h₂').symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_hom_of_isPullback_left (C.isPullback₃ i j k) o₁.base o₂.base e
  obtain ⟨ε, hε, hε₁⟩ := exists_complexesHom_lift (C.c₁₂ i j k) t o₁ ht₁
  have hε₂ : ε.comp (C.c₂₃ i j k) = o₂ := by
    refine complexesHom_cancel_right (C.n j k) ?_ ?_
    · show ε.base ≫ (C.c₂₃ i j k).base = o₂.base
      rw [hε, ht₂]
    · rw [ComplexesHom.assoc, ← C.comp₂, ← ComplexesHom.assoc, hε₁, h₂, h₂']
  refine ⟨ε.comp (C.c₁₃ i j k), ?_, ?_⟩
  · rw [ComplexesHom.assoc, ← C.comp₁, ← ComplexesHom.assoc, hε₁, h₁]
  · rw [ComplexesHom.assoc, ← C.comp₃, ← ComplexesHom.assoc, hε₂, h₃]

/-- The relation is reflexive. -/
theorem IsRelated.refl {i : I} (x : ComplexesHom A (C.X i)) : C.IsRelated x x := by
  obtain ⟨x', -, h⟩ := IsRelated.exists_left x i x.base rfl
  obtain ⟨w, hw, h'⟩ := IsRelated.exists_right x i x.base rfl
  have e : x = w := IsRelated.unique h (h.trans h') hw.symm
  rwa [← e] at h'

/-- The relation is symmetric. -/
theorem IsRelated.symm {i j : I} {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)}
    (h : C.IsRelated x y) : C.IsRelated y x := by
  obtain ⟨w, hw, h'⟩ := IsRelated.exists_right y i x.base h.base_w.symm
  have e : x = w := IsRelated.unique (IsRelated.refl x) (h.trans h') hw.symm
  rwa [← e] at h'

/-- The relation is stable under composition on the left. -/
theorem IsRelated.comp_left {A' : ComplexesObject D} (g : ComplexesHom A' A) {i j : I}
    {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)} (h : C.IsRelated x y) :
    C.IsRelated (g.comp x) (g.comp y) := by
  obtain ⟨o, rfl, rfl⟩ := h
  exact ⟨g.comp o, ComplexesHom.assoc _ _ _, ComplexesHom.assoc _ _ _⟩

end Related

namespace SmallRefinement

variable {C : CechCover T I} (R : C.SmallRefinement)

/-! ### The members of a refinement in `Complexes_{X/Y}` -/

section Members

/-- The complex `K_{σ k}` pulled back to the member `W_k` of a refinement, as an object of
`Complexes_{X/Y}`. -/
abbrev memberObject (k : R.ι) : ComplexesObject D :=
  restrictComplex (C.X (R.σ k)) (R.memberMap k)

/-- The canonical morphism from `K_{σ k}|_{W_k}` to `K_{σ k}`, over `W_k ⟶ T_{σ k}`. -/
abbrev memberToCover (k : R.ι) : ComplexesHom (R.memberObject k) (C.X (R.σ k)) :=
  restrictComplexHom (C.X (R.σ k)) (R.memberMap k)

/-- The morphism from `K_{σ k}|_{W_k}` to `K_0`, over the injection `W_k ⟶ V`. -/
abbrev memberToUnion (k : R.ι) : ComplexesHom (R.memberObject k) R.unionComplex :=
  ⟨R.memberIncl k, (R.unionObjectIso k).hom, Iso.isIso_hom _⟩

/-- The pieces `Z ×_V W_k` of a test scheme over the disjoint union are fibre products. -/
theorem isPullback_piece_left {Z : SchemesOver D.Y} (c : Z ⟶ R.unionTest) (k : R.ι) :
    IsPullback (R.pieceHom c k).left (R.pieceMember c k).left c.left (R.memberIncl k).left :=
  IsPullback.of_hasPullback c.left (R.j k)

variable {A X : ComplexesObject D}

/-- The restriction of a morphism `a : A ⟶ K_0` to a piece of `A` factors through
`K_{σ k}|_{W_k} ⟶ K_0`. -/
theorem exists_pieceLift (a : ComplexesHom A R.unionComplex) (k : R.ι) :
    ∃ l : ComplexesHom (restrictComplex A (R.pieceHom a.base k)) (R.memberObject k),
      l.base = R.pieceMember a.base k ∧
        l.comp (R.memberToUnion k) = (restrictComplexHom A (R.pieceHom a.base k)).comp a :=
  exists_complexesHom_lift (R.memberToUnion k) (R.pieceMember a.base k)
    ((restrictComplexHom A (R.pieceHom a.base k)).comp a) (R.pieceHom_comp a.base k).symm

/-- **Morphisms of `Complexes_{X/Y}` glue from the pieces**, given as morphisms over the
restrictions of a base map. -/
theorem exists_complexesHom_of_pieces' (c : A.T ⟶ R.unionTest) (b : A.T ⟶ X.T)
    (g : ∀ k, ComplexesHom (restrictComplex A (R.pieceHom c k)) X)
    (hg : ∀ k, R.pieceHom c k ≫ b = (g k).base) :
    ∃ g' : ComplexesHom A X, g'.base = b ∧
      ∀ k, (restrictComplexHom A (R.pieceHom c k)).comp g' = g k := by
  obtain ⟨g', hb, hk⟩ := R.exists_complexesHom_of_pieces c b
    fun k => (D.relativeMapComparison (hg k)).app X.E ≪≫
      @asIso _ _ _ _ (g k).fibre (g k).isIso_fibre
  exact ⟨g', hb, fun k => (hk k).trans (complexesHom_mk_trans_eq (g k) (hg k))⟩

end Members

/-! ### Morphisms to `K_0` related to morphisms to the members -/

section UnionRelated

variable {A : ComplexesObject D}

/-- **A morphism `a : A ⟶ K_0` and a morphism `x : A ⟶ K_i` are related** when their base maps
agree over `T` and, on every piece `A|_{Z ×_V W_k}`, the factorization of `a` through
`K_{σ k}|_{W_k}` followed by `K_{σ k}|_{W_k} ⟶ K_{σ k}` is related to the restriction of `x`. -/
def IsUnionRelated (a : ComplexesHom A R.unionComplex) {i : I} (x : ComplexesHom A (C.X i)) :
    Prop :=
  x.base ≫ C.a i = a.base ≫ R.unionHom ∧
    ∀ (k : R.ι) (l : ComplexesHom (restrictComplex A (R.pieceHom a.base k)) (R.memberObject k)),
      l.base = R.pieceMember a.base k →
      l.comp (R.memberToUnion k) = (restrictComplexHom A (R.pieceHom a.base k)).comp a →
      C.IsRelated (l.comp (R.memberToCover k))
        ((restrictComplexHom A (R.pieceHom a.base k)).comp x)

variable {R}

/-- The base condition of a related pair, on a piece. -/
theorem pieceMember_memberMap_w {Z : SchemesOver D.Y} (c : Z ⟶ R.unionTest) (k : R.ι) :
    (R.pieceMember c k ≫ R.memberMap k) ≫ C.a (R.σ k) =
      R.pieceHom c k ≫ c ≫ R.unionHom := by
  rw [Category.assoc, R.memberMap_comp_a, ← Category.assoc, ← R.pieceHom_comp, Category.assoc]

/-- The base condition on a piece, for a base map to `T` agreeing with `c` over `T`. -/
private theorem pieceMember_memberMap_w_of_comp_eq {A : ComplexesObject D} {W : SchemesOver D.Y}
    (c : A.T ⟶ R.unionTest) (b : A.T ⟶ W) (r : W ⟶ T) (hb : b ≫ r = c ≫ R.unionHom) (k : R.ι) :
    (R.pieceMember c k ≫ R.memberMap k) ≫ C.a (R.σ k) = (R.pieceHom c k ≫ b) ≫ r := by
  rw [pieceMember_memberMap_w, Category.assoc, hb]

/-- Morphisms from the pieces to the members glue to a morphism to `K_0`. -/
private theorem exists_complexesHom_of_member_pieces {A : ComplexesObject D}
    (c : A.T ⟶ R.unionTest)
    (l : ∀ k, ComplexesHom (restrictComplex A (R.pieceHom c k)) (R.memberObject k))
    (hl : ∀ k, (l k).base = R.pieceMember c k) :
    ∃ a : ComplexesHom A R.unionComplex, a.base = c ∧
      ∀ k, (restrictComplexHom A (R.pieceHom c k)).comp a = (l k).comp (R.memberToUnion k) :=
  R.exists_complexesHom_of_pieces' c c (fun k => (l k).comp (R.memberToUnion k)) fun k => by
    change _ = (l k).base ≫ R.memberIncl k
    rw [hl k]
    exact R.pieceHom_comp c k

/-- Restricting along `g : A' ⟶ A` is compatible with the factorizations of `a` and `g ≫ a`
through `K_{σ k}|_{W_k}`. -/
private theorem exists_pieceComp {A A' : ComplexesObject D} (a : ComplexesHom A R.unionComplex)
    (g : ComplexesHom A' A) (k : R.ι)
    (l₀ : ComplexesHom (restrictComplex A (R.pieceHom a.base k)) (R.memberObject k))
    (hl₀ : l₀.base = R.pieceMember a.base k)
    (hl₀' : l₀.comp (R.memberToUnion k) = (restrictComplexHom A (R.pieceHom a.base k)).comp a) :
    ∃ κ : ComplexesHom (restrictComplex A' (R.pieceHom (g.comp a).base k))
        (restrictComplex A (R.pieceHom a.base k)),
      (∀ l : ComplexesHom (restrictComplex A' (R.pieceHom (g.comp a).base k)) (R.memberObject k),
        l.base = R.pieceMember (g.comp a).base k →
        l.comp (R.memberToUnion k) =
          (restrictComplexHom A' (R.pieceHom (g.comp a).base k)).comp (g.comp a) →
        l = κ.comp l₀) ∧
      ∀ {Z : ComplexesObject D} (x : ComplexesHom A Z),
        κ.comp ((restrictComplexHom A (R.pieceHom a.base k)).comp x) =
          (restrictComplexHom A' (R.pieceHom (g.comp a).base k)).comp (g.comp x) := by
  obtain ⟨t, ht₁, ht₂⟩ := exists_hom_of_isPullback_left (R.isPullback_piece_left a.base k)
    (R.pieceHom (g.comp a).base k ≫ g.base) (R.pieceMember (g.comp a).base k)
    ((Category.assoc _ _ _).trans (R.pieceHom_comp (g.comp a).base k))
  obtain ⟨κ, hκ, hκ'⟩ := exists_complexesHom_lift (restrictComplexHom A (R.pieceHom a.base k)) t
    ((restrictComplexHom A' (R.pieceHom (g.comp a).base k)).comp g) ht₁
  refine ⟨κ, fun l hl hl' => ?_, fun x => by
    rw [← ComplexesHom.assoc, hκ', ComplexesHom.assoc]⟩
  refine complexesHom_cancel_right (R.memberToUnion k) ?_ ?_
  · change l.base = κ.base ≫ l₀.base
    rw [hl, hκ, hl₀, ht₂]
  · rw [hl', ComplexesHom.assoc κ, hl₀', ← ComplexesHom.assoc κ, hκ', ComplexesHom.assoc]

variable (R) in
/-- A morphism to `K_0` is related to a morphism to the member `K_i` over every base map to `T_i`
agreeing over `T`. -/
theorem IsUnionRelated.exists_member (a : ComplexesHom A R.unionComplex) (i : I)
    (z : A.T ⟶ (C.X i).T) (hz : z ≫ C.a i = a.base ≫ R.unionHom) :
    ∃ x : ComplexesHom A (C.X i), x.base = z ∧ R.IsUnionRelated a x := by
  choose l hl hl' using R.exists_pieceLift a
  have hw : ∀ k, ((l k).comp (R.memberToCover k)).base ≫ C.a (R.σ k) =
      (R.pieceHom a.base k ≫ z) ≫ C.a i := fun k => by
    show ((l k).base ≫ R.memberMap k) ≫ C.a (R.σ k) = _
    rw [hl k, pieceMember_memberMap_w, Category.assoc, hz]
  choose x hx hxr using fun k =>
    IsRelated.exists_right ((l k).comp (R.memberToCover k)) i (R.pieceHom a.base k ≫ z) (hw k)
  obtain ⟨g, hg, hgk⟩ := R.exists_complexesHom_of_pieces' a.base z x fun k => (hx k).symm
  refine ⟨g, hg, by rw [hg, hz], fun k l' hb hc => ?_⟩
  have e : l' = l k := complexesHom_cancel_right (R.memberToUnion k) (hb.trans (hl k).symm)
    (hc.trans (hl' k).symm)
  subst e
  rw [hgk k]
  exact hxr k

variable (R) in
/-- A morphism to a member `K_i` is related to a morphism to `K_0` over every base map to `V`
agreeing over `T`. -/
theorem IsUnionRelated.exists_unionHom {i : I} (x : ComplexesHom A (C.X i))
    (c : A.T ⟶ R.unionTest) (hc : x.base ≫ C.a i = c ≫ R.unionHom) :
    ∃ a : ComplexesHom A R.unionComplex, a.base = c ∧ R.IsUnionRelated a x := by
  choose y hy hyr using fun k => IsRelated.exists_left
    ((restrictComplexHom A (R.pieceHom c k)).comp x) (R.σ k) _
    (pieceMember_memberMap_w_of_comp_eq c x.base _ hc k)
  choose l hl hl' using fun k =>
    exists_complexesHom_lift (R.memberToCover k) (R.pieceMember c k) (y k) (hy k).symm
  obtain ⟨a, ha, hak⟩ := exists_complexesHom_of_member_pieces c l hl
  refine ⟨a, ha, ?_⟩
  subst ha
  refine ⟨hc, fun k l' hb hc' => ?_⟩
  have e : l' = l k := complexesHom_cancel_right (R.memberToUnion k) (hb.trans (hl k).symm)
    (hc'.trans (hak k))
  subst e
  rw [hl' k]
  exact hyr k

/-- A morphism to `K_0` is related to at most one morphism over a given base map to a member. -/
theorem IsUnionRelated.unique_member {a : ComplexesHom A R.unionComplex} {i : I}
    {x x' : ComplexesHom A (C.X i)} (h : R.IsUnionRelated a x) (h' : R.IsUnionRelated a x')
    (hb : x.base = x'.base) : x = x' :=
  R.complexesHom_ext_pieces a.base hb fun k => by
    obtain ⟨l, hl, hl'⟩ := R.exists_pieceLift a k
    exact IsRelated.unique (h.2 k l hl hl') (h'.2 k l hl hl')
      (congrArg (R.pieceHom a.base k ≫ ·) hb)

/-- A morphism to a member is related to at most one morphism to `K_0` over a given base map. -/
theorem IsUnionRelated.unique_union {a a' : ComplexesHom A R.unionComplex} {i : I}
    {x : ComplexesHom A (C.X i)} (h : R.IsUnionRelated a x) (h' : R.IsUnionRelated a' x)
    (hb : a.base = a'.base) : a = a' := by
  obtain ⟨b', f', i'⟩ := a'
  change a.base = b' at hb
  subst hb
  refine R.complexesHom_ext_pieces a.base rfl fun k => ?_
  obtain ⟨l, hl, hl'⟩ := R.exists_pieceLift a k
  obtain ⟨l', hlb', hl''⟩ := R.exists_pieceLift ⟨a.base, f', i'⟩ k
  have r₁ := h.2 k l hl hl'
  have r₂ := h'.2 k l' hlb' hl''
  have e₁ : l.comp (R.memberToCover k) = l'.comp (R.memberToCover k) :=
    IsRelated.unique (IsRelated.refl _) (r₁.trans r₂.symm)
      (by change l.base ≫ _ = l'.base ≫ _; rw [hl, hlb'])
  have e₂ : l = l' := complexesHom_cancel_right (R.memberToCover k) (hl.trans hlb'.symm) e₁
  subst e₂
  exact hl'.symm.trans hl''

variable (R) in
/-- The relation is stable under composition on the left. -/
theorem IsUnionRelated.comp_left {a : ComplexesHom A R.unionComplex} {i : I}
    {x : ComplexesHom A (C.X i)} (h : R.IsUnionRelated a x) {A' : ComplexesObject D}
    (g : ComplexesHom A' A) : R.IsUnionRelated (g.comp a) (g.comp x) := by
  refine ⟨?_, fun k l hl hl' => ?_⟩
  · show (g.base ≫ x.base) ≫ C.a i = (g.base ≫ a.base) ≫ R.unionHom
    rw [Category.assoc, Category.assoc, h.1]
  obtain ⟨l₀, hl₀, hl₀'⟩ := R.exists_pieceLift a k
  obtain ⟨κ, he, hκ⟩ := exists_pieceComp a g k l₀ hl₀ hl₀'
  obtain rfl := he l hl hl'
  have h₁ := (h.2 k l₀ hl₀ hl₀').comp_left κ
  rw [hκ x, ← ComplexesHom.assoc] at h₁
  exact h₁

/-- A related pair stays related after replacing the morphism to the member by a related one. -/
theorem IsUnionRelated.of_isRelated {a : ComplexesHom A R.unionComplex} {i j : I}
    {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)} (h : R.IsUnionRelated a x)
    (h' : C.IsRelated x y) : R.IsUnionRelated a y :=
  ⟨h'.base_w.symm.trans h.1, fun k l hl hl' => (h.2 k l hl hl').trans (h'.comp_left _)⟩

/-- Two morphisms to members related to one morphism to `K_0` are related. -/
theorem IsUnionRelated.isRelated {a : ComplexesHom A R.unionComplex} {i j : I}
    {x : ComplexesHom A (C.X i)} {y : ComplexesHom A (C.X j)} (h : R.IsUnionRelated a x)
    (h' : R.IsUnionRelated a y) : C.IsRelated x y := by
  obtain ⟨y', hy', hr⟩ := IsRelated.exists_right x j y.base (h.1.trans h'.1.symm)
  have e : y' = y := IsUnionRelated.unique_member (h.of_isRelated hr) h' hy'
  rwa [e] at hr

end UnionRelated

/-! ### The descent datum of `K_0` -/

section Transport

variable {A : ComplexesObject D}

/-- **Two morphisms `a, a' : A ⟶ K_0` differ by the gluing isomorphisms** when every morphism to
a member related to a restriction of `a` is related to the same restriction of `a'`. -/
def IsUnionTransport (a a' : ComplexesHom A R.unionComplex) : Prop :=
  ∀ (A' : ComplexesObject D) (g : ComplexesHom A' A) (i : I) (x : ComplexesHom A' (C.X i)),
    R.IsUnionRelated (g.comp a) x → R.IsUnionRelated (g.comp a') x

variable {R}

variable (R) in
/-- **The transport of a morphism to `K_0`** along every other base map to `V` agreeing over
`T` exists. -/
theorem IsUnionTransport.exists (a : ComplexesHom A R.unionComplex) (c' : A.T ⟶ R.unionTest)
    (hc : a.base ≫ R.unionHom = c' ≫ R.unionHom) :
    ∃ a' : ComplexesHom A R.unionComplex, a'.base = c' ∧ R.IsUnionTransport a a' := by
  choose x hx hxr using fun k => IsUnionRelated.exists_member R
    ((restrictComplexHom A (R.pieceHom c' k)).comp a) (R.σ k) _
    (pieceMember_memberMap_w_of_comp_eq c' a.base _ hc k)
  choose l hl hl' using fun k =>
    exists_complexesHom_lift (R.memberToCover k) (R.pieceMember c' k) (x k) (hx k).symm
  obtain ⟨a', ha', hak⟩ := exists_complexesHom_of_member_pieces c' l hl
  refine ⟨a', ha', ?_⟩
  subst ha'
  intro A'' g i y hy
  refine ⟨?_, fun k l'' hl₁ hl₂ => ?_⟩
  · show y.base ≫ C.a i = (g.base ≫ a'.base) ≫ R.unionHom
    rw [hy.1, Category.assoc, ← hc]
    rfl
  obtain ⟨κ, he, hκ⟩ := exists_pieceComp a' g k (l k) (hl k) (hak k).symm
  obtain rfl := he l'' hl₁ hl₂
  rw [ComplexesHom.assoc, hl' k]
  refine IsUnionRelated.isRelated ((hxr k).comp_left R κ) ?_
  rw [hκ a]
  exact hy.comp_left R _

/-- The transport relation is stable under composition on the left. -/
theorem IsUnionTransport.comp_left {a a' : ComplexesHom A R.unionComplex}
    (h : R.IsUnionTransport a a') {A' : ComplexesObject D} (g : ComplexesHom A' A) :
    R.IsUnionTransport (g.comp a) (g.comp a') := fun A'' g' i x hx => by
  rw [← ComplexesHom.assoc] at hx ⊢
  exact h A'' (g'.comp g) i x hx

/-- The transport relation is transitive. -/
theorem IsUnionTransport.trans {a a' a'' : ComplexesHom A R.unionComplex}
    (h : R.IsUnionTransport a a') (h' : R.IsUnionTransport a' a'') : R.IsUnionTransport a a'' :=
  fun A'' g i x hx => h' A'' g i x (h A'' g i x hx)

/-- A morphism to a member related to `a` is related to every transport of `a`. -/
theorem IsUnionTransport.isUnionRelated {a a' : ComplexesHom A R.unionComplex}
    (h : R.IsUnionTransport a a') {i : I} {x : ComplexesHom A (C.X i)} (hx : R.IsUnionRelated a x) :
    R.IsUnionRelated a' x := by
  have h' := h A (ComplexesHom.id A) i x (by rwa [ComplexesHom.id_comp])
  rwa [ComplexesHom.id_comp] at h'

/-- **The transport is unique** over a given base map. -/
theorem IsUnionTransport.unique {a a' a'' : ComplexesHom A R.unionComplex}
    (h : R.IsUnionTransport a a')
    (h' : R.IsUnionTransport a a'') (hc : a.base ≫ R.unionHom = a'.base ≫ R.unionHom)
    (hb : a'.base = a''.base) : a' = a'' := by
  obtain ⟨b'', f'', i''⟩ := a''
  change a'.base = b'' at hb
  subst hb
  refine R.complexesHom_ext_pieces a'.base rfl fun k => ?_
  obtain ⟨x, -, hx⟩ := IsUnionRelated.exists_member R
    ((restrictComplexHom A (R.pieceHom a'.base k)).comp a) (R.σ k) _
    (pieceMember_memberMap_w_of_comp_eq a'.base a.base _ hc k)
  exact IsUnionRelated.unique_union (h _ _ _ x hx) (h' _ _ _ x hx) rfl

end Transport

/-! ### Negative self-extensions of objects over the disjoint union -/

/-- **An object of `Complexes_{X/Y}` mapping to `K_0` has no negative self-extensions** as soon
as every base change of every member of the covering has none: on each piece over `W_k` it is a
base change of `K_{σ k}`, and morphisms on the disjoint union are families of morphisms on the
pieces. -/
theorem subsingleton_shift_of_hom_unionComplex
    (hneg : ∀ (i : I) (V : SchemesOver D.Y) (h : V ⟶ (C.X i).T) (n : ℤ), n < 0 →
      Subsingleton
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E)⟦n⟧))
    {A : ComplexesObject D} (a : ComplexesHom A R.unionComplex) (t : ℤ) (ht : t < 0) :
    Subsingleton (A.E ⟶ A.E⟦t⟧) := by
  refine ⟨fun f g => hom_ext_of_isPullback_cofan R.isColimit (R.isPullback_piece a.base)
    fun k => ?_⟩
  obtain ⟨l, -, -⟩ := R.exists_pieceLift a k
  have hs := hneg (R.σ k) _ (l.comp (R.memberToCover k)).base t ht
  have e : Subsingleton ((restrictComplex A (R.pieceHom a.base k)).E ⟶
      (restrictComplex A (R.pieceHom a.base k)).E⟦t⟧) :=
    Equiv.subsingleton ((@asIso _ _ _ _ _ (l.comp (R.memberToCover k)).isIso_fibre).homCongr
      ((shiftFunctor _ t).mapIso
        (@asIso _ _ _ _ _ (l.comp (R.memberToCover k)).isIso_fibre))).symm
  exact (Iso.cancel_iso_hom_right _ _ ((((smallEtaleDerivedPullbackData B S hS).pull
    (D.relativeMap (R.pieceHom a.base k))).commShiftIso t).app A.E)).1 (e.elim _ _)

end SmallRefinement

end CechCover

end ComplexesSituation

end AlgebraicGeometry.Space

end
