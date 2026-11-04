module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent

/-!
# Descent data and sheaves: descent of morphisms, full faithfulness and effectivity

Let `{X i ⟶ T}` be an fppf covering of algebraic spaces and let `F` be a space over `T`. A
scheme-valued point of `T` factors through a member of the covering after restriction along a
covering sieve, so a point of `F` lifts, locally, to a point of one of the fibre products
`X i ×_T F`. Consequently the fibre products are jointly an effective epimorphism onto
sheaves: a family of morphisms out of them which cannot distinguish two points with the same
image in `F` descends to a unique morphism out of `F`.

Applied to the components of a morphism of descent data, this says that the functor from
sheaves over `T` whose fibre products with the covering are algebraic spaces to descent data
relative to the covering is **fully faithful**. Combined with the identification of the
descent datum of an algebraic space over `T` with its canonical descent datum, it gives part
(2) of the lemma: such a sheaf is an algebraic space exactly when its descent datum is
effective.

## Main definitions

* `AlgebraicGeometry.Space.Descent.FibreCompatible` is the compatibility a family of
  morphisms out of the fibre products `X i ×_T F` must satisfy in order to descend to `F`.
* `AlgebraicGeometry.Space.Descent.fibreDescentFunctorFullyFaithful` is the full faithfulness
  of `AlgebraicGeometry.Space.Descent.fibreDescentFunctor`.
* `AlgebraicGeometry.Space.Descent.trivDatum` and
  `AlgebraicGeometry.Space.Descent.canDatum` present the canonical descent datum of an
  algebraic space over `T` as the pullback of its trivial descent datum along the family,
  `AlgebraicGeometry.Space.Descent.canComponentIso` identifies its components with the fibre
  products, and `AlgebraicGeometry.Space.Descent.canonicalIsoFibreDescentData` is the
  resulting isomorphism of descent data.

## Main results

* `AlgebraicGeometry.Space.Descent.existsUnique_desc_of_fibreCompatible`: the fibre products
  of an fppf covering with a space over its target are jointly an effective epimorphism onto
  sheaves.
* `AlgebraicGeometry.Space.Descent.existsUnique_hom_map_fibreDescentFunctor`: every morphism
  between the descent data of two such sheaves comes from a unique morphism of sheaves over
  `T`.
* `AlgebraicGeometry.Space.Descent.familyCanonical_obj_eq` and
  `AlgebraicGeometry.Space.Descent.canComponentIso_comm` are the two halves of the
  identification of the canonical descent datum: its components are the fibre products, and
  the identification is compatible with the gluing isomorphisms.
* `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_iff_isEffective_fibreDescentData`: the
  descent datum of such a sheaf is effective exactly when the sheaf is an algebraic space.

## Implementation notes

Hypotheses carried explicitly rather than derived. The family `f` is assumed to be an fppf
covering of algebraic spaces, `AlgebraicGeometry.Space.IsFppfCovering`, Tag 03Y8; it enters
only through `AlgebraicGeometry.Space.exists_sieve_factorization_of_isFppfCovering`, which
supplies the local factorizations, and through nothing else. The target `T` and the members
`X i` are assumed to be algebraic spaces, as the category of descent data requires; `T` being
an algebraic space is used a second time, through its sheaf condition, to see that a
descended morphism lies over `T`. The target of a descended morphism is assumed to satisfy
the fppf sheaf condition. For a sheaf over `T` in
`AlgebraicGeometry.Space.Descent.SheavesWithSpaceFibres` both the sheaf condition and the
algebraicity of all its fibre products are part of the data of the object; the sheaf
condition of the *target* of a morphism is what the descent uses, and algebraicity of the
fibre products is not used by the descent at all — it is needed only to have a descent datum
in the first place.

What is **not** reached. The functor in the other direction, which the source constructs as
the coequalizer of `∐_{i,j} V i ×_T X j ⇉ ∐_i V i`, is not formalized, so essential
surjectivity of `AlgebraicGeometry.Space.Descent.fibreDescentFunctor` is absent and the
**equivalence of categories** asserted by Tag 0ADT is *not* proved here: only its full
faithfulness, which is one of the two halves. The two natural isomorphisms exhibiting the
pair of functors as quasi-inverse are likewise absent. The equivalence of Tag 0ADK between
descent data for a family and for its sheaf coproduct is not used on this route. Tag 0ADV,
which the source's footnote invokes for the unconditional statement that the coequalizer
sheaf is an algebraic space when the index type is not too large, is **not** needed for part
(2) as proved here and is not available in this library: effectivity of the descent datum
already supplies an algebraic space over `T`, and full faithfulness then identifies the sheaf
with it. The unconditional statement remains out of reach.

The compatibility `AlgebraicGeometry.Space.Descent.FibreCompatible` is stated for an
arbitrary presheaf of test objects rather than on the fibre product of two of the
`X i ×_T F`; the two are equivalent, and the former is the shape every step of the descent
consumes, as in
`StacksFrontier/AlgebraicGeometry/Spaces/FppfMorphismDescent.lean`. For a morphism of descent
data it is verified from the gluing compatibility by way of the move operation
`CategoryTheory.FamilyTransport`: a point of `X i ×_T F` and a point of `X j` over the same
test object are the two coordinates of a point of `X j ×_T F`, and
`AlgebraicGeometry.Space.Descent.DescentData.move_naturality` is exactly the independence
needed. The roundtrip identity recovering a move operation from its gluing isomorphism is
restated here privately as `move_eq_lift_gluing`, since
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/SpacesOverSpaces/Transport.lean` does not carry
it; the local-section construction is modelled on the private
`existsUnique_localSection_fppf` of `FppfMorphismDescent.lean` and is restated here because
that one descends along the covering itself rather than along its fibre products with `F`.

The canonical descent datum is reached through
`AlgebraicGeometry.Space.Descent.PullbackFunctor.obj_eq`, which identifies it with the datum
produced by `AlgebraicGeometry.Space.Descent.pullbackDatum`; the component pullback squares
and the base-change equation for the gluing isomorphisms of that structure are the only
access to its gluing. The four object equations carried by
`AlgebraicGeometry.Space.Descent.PulledBackDatum` hold definitionally, so the `eqToHom`s in
its `gluing_comm` are definitionally identities and are discharged by a type ascription
rather than by transport.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 0ADQ](https://stacks.math.columbia.edu/tag/0ADQ)
* [Stacks Project, Tag 0ADR](https://stacks.math.columbia.edu/tag/0ADR)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T)

/-! ### Local factorizations of a section through a fibre product -/

/-- A section of a space over `T` factors, after restriction along a covering sieve, through
one of the fibre products `X i ×_T F`. -/
private lemma exists_sieve_fibreFactorization
    (hcov : Space.IsFppfCovering B S hS X f) (F : Over T) (W : BigFppfOver B S hS)
    (y : F.left.obj (op W)) :
    ∃ R : Sieve W, R ∈ BigFppfOver.topology B S hS W ∧
      ∀ ⦃W' : BigFppfOver B S hS⦄ (k : W' ⟶ W), R k →
        ∃ (i : ι) (b : yoneda.obj W' ⟶ pullback F.hom (f i)),
          b ≫ pullback.fst F.hom (f i) = yoneda.map k ≫ yonedaEquiv.symm y := by
  obtain ⟨R, hR, hlift⟩ := Space.exists_sieve_factorization_of_isFppfCovering B S hS X f hcov W
    (yonedaEquiv.symm y ≫ F.hom)
  refine ⟨R, hR, fun {W'} k hk ↦ ?_⟩
  obtain ⟨i, η, hη⟩ := hlift k hk
  exact ⟨i, pullback.lift (yoneda.map k ≫ yonedaEquiv.symm y) η (by
    rw [hη, Category.assoc]), pullback.lift_fst _ _ _⟩

/-! ### The fibre products of a covering are jointly an effective epimorphism -/

section Descend

variable (F : Over T) {Gl : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The compatibility a family of morphisms out of the fibre products `X i ×_T F` must satisfy
in order to descend to `F`: any two points of fibre products with the same image in `F` have
the same image under it. -/
public abbrev FibreCompatible (g : ∀ i, pullback F.hom (f i) ⟶ Gl) : Prop :=
  ∀ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i j : ι) (a : Q ⟶ pullback F.hom (f i))
    (b : Q ⟶ pullback F.hom (f j)),
    a ≫ pullback.fst F.hom (f i) = b ≫ pullback.fst F.hom (f j) → a ≫ g i = b ≫ g j

/-- The section of the target determined by a compatible family of morphisms out of the fibre
products: it is pinned down by its restrictions along the local factorizations. -/
private theorem existsUnique_localFibreSection
    (hcov : Space.IsFppfCovering B S hS X f)
    (hGl : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Gl)
    (g : ∀ i, pullback F.hom (f i) ⟶ Gl) (hg : FibreCompatible f F g)
    (W : BigFppfOver B S hS) (y : F.left.obj (op W)) :
    ∃! z : Gl.obj (op W),
      ∀ (W' : BigFppfOver B S hS) (k : W' ⟶ W) (i : ι)
        (b : yoneda.obj W' ⟶ pullback F.hom (f i)),
        b ≫ pullback.fst F.hom (f i) = yoneda.map k ≫ yonedaEquiv.symm y →
        Gl.map k.op z = yonedaEquiv (b ≫ g i) := by
  classical
  let J := BigFppfOver.topology B S hS
  have hGl' : Presieve.IsSheaf J Gl := (isSheaf_iff_isSheaf_of_type J Gl).mp hGl
  obtain ⟨R, hR, hlift⟩ := exists_sieve_fibreFactorization f hcov F W y
  choose idx locMap hlocSpec using
    fun (W' : BigFppfOver B S hS) (k : W' ⟶ W) (hk : R k) ↦ hlift k hk
  let x : Presieve.FamilyOfElements Gl R.arrows := fun W' k hk ↦
    yonedaEquiv (locMap W' k hk ≫ g (idx W' k hk))
  have hx : x.Compatible := by
    intro W₁ W₂ P e₁ e₂ k₁ k₂ h₁ h₂ hcomm
    have hbase : (yoneda.map e₁ ≫ locMap W₁ k₁ h₁) ≫
          pullback.fst F.hom (f (idx W₁ k₁ h₁)) =
        (yoneda.map e₂ ≫ locMap W₂ k₂ h₂) ≫ pullback.fst F.hom (f (idx W₂ k₂ h₂)) := by
      rw [Category.assoc, Category.assoc, hlocSpec, hlocSpec, ← Category.assoc,
        ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, hcomm]
    have hcompat := hg (yoneda.obj P) _ _ _ _ hbase
    show Gl.map e₁.op (x k₁ h₁) = Gl.map e₂.op (x k₂ h₂)
    simp only [x, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv (by simpa only [Category.assoc] using hcompat)
  obtain ⟨z, hz, hzu⟩ := hGl' R hR x hx
  refine ⟨z, ?_, ?_⟩
  · intro W' k i b hb
    refine (hGl' (R.pullback k) (J.pullback_stable k hR)).isSeparatedFor.ext ?_
    intro W'' r hr
    have hrR : R (r ≫ k) := hr
    have hfac : locMap W'' (r ≫ k) hrR ≫ pullback.fst F.hom (f (idx W'' (r ≫ k) hrR)) =
        (yoneda.map r ≫ b) ≫ pullback.fst F.hom (f i) := by
      rw [hlocSpec, Category.assoc, hb, ← Category.assoc, ← yoneda.map_comp]
    calc
      Gl.map r.op (Gl.map k.op z) = Gl.map (r ≫ k).op z := by
        rw [← Functor.map_comp_apply, ← op_comp]
      _ = x (r ≫ k) hrR := hz _ hrR
      _ = yonedaEquiv ((yoneda.map r ≫ b) ≫ g i) :=
        congrArg yonedaEquiv (by
          simpa only [Category.assoc] using hg (yoneda.obj W'') _ _ _ _ hfac)
      _ = Gl.map r.op (yonedaEquiv (b ≫ g i)) := by
        rw [yonedaEquiv_naturality, Category.assoc]
  · intro z' hz'
    refine (hGl' R hR).isSeparatedFor.ext ?_
    intro W' k hk
    exact (hz' W' k (idx W' k hk) (locMap W' k hk) (hlocSpec W' k hk)).trans (hz k hk).symm

/-- **The fibre products of an fppf covering are jointly an effective epimorphism onto
sheaves.** For an fppf covering `X i ⟶ T` of algebraic spaces and a space `F` over `T`, a
compatible family of morphisms from the fibre products `X i ×_T F` to a sheaf descends to a
unique morphism from `F`. -/
public theorem existsUnique_desc_of_fibreCompatible
    (hcov : Space.IsFppfCovering B S hS X f)
    (hGl : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Gl)
    (g : ∀ i, pullback F.hom (f i) ⟶ Gl) (hg : FibreCompatible f F g) :
    ∃! d : F.left ⟶ Gl, ∀ i, pullback.fst F.hom (f i) ≫ d = g i := by
  classical
  let loc := fun (W : BigFppfOver B S hS) (y : F.left.obj (op W)) ↦
    existsUnique_localFibreSection f F hcov hGl g hg W y
  let sect : ∀ W : BigFppfOver B S hS, F.left.obj (op W) → Gl.obj (op W) :=
    fun W y ↦ (loc W y).choose
  have sect_spec : ∀ (W : BigFppfOver B S hS) (y : F.left.obj (op W))
      (W' : BigFppfOver B S hS) (k : W' ⟶ W) (i : ι)
      (b : yoneda.obj W' ⟶ pullback F.hom (f i)),
      b ≫ pullback.fst F.hom (f i) = yoneda.map k ≫ yonedaEquiv.symm y →
      Gl.map k.op (sect W y) = yonedaEquiv (b ≫ g i) :=
    fun W y ↦ (loc W y).choose_spec.1
  have sect_uniq : ∀ (W : BigFppfOver B S hS) (y : F.left.obj (op W)) (z : Gl.obj (op W)),
      (∀ (W' : BigFppfOver B S hS) (k : W' ⟶ W) (i : ι)
        (b : yoneda.obj W' ⟶ pullback F.hom (f i)),
        b ≫ pullback.fst F.hom (f i) = yoneda.map k ≫ yonedaEquiv.symm y →
        Gl.map k.op z = yonedaEquiv (b ≫ g i)) → z = sect W y :=
    fun W y ↦ (loc W y).choose_spec.2
  have key : ∀ d : F.left ⟶ Gl, (∀ i, pullback.fst F.hom (f i) ≫ d = g i) →
      ∀ (W W' : BigFppfOver B S hS) (y : F.left.obj (op W)) (q : W' ⟶ W) (i : ι)
        (b : yoneda.obj W' ⟶ pullback F.hom (f i)),
        b ≫ pullback.fst F.hom (f i) = yoneda.map q ≫ yonedaEquiv.symm y →
        Gl.map q.op (d.app (op W) y) = yonedaEquiv (b ≫ g i) := by
    intro d hd W W' y q i b hb
    have hy : yonedaEquiv (b ≫ pullback.fst F.hom (f i)) = F.left.map q.op y := by
      rw [hb, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    calc Gl.map q.op (d.app (op W) y)
        = d.app (op W') (F.left.map q.op y) := by rw [NatTrans.naturality_apply]
      _ = d.app (op W') (yonedaEquiv (b ≫ pullback.fst F.hom (f i))) := by rw [hy]
      _ = yonedaEquiv ((b ≫ pullback.fst F.hom (f i)) ≫ d) := (yonedaEquiv_comp _ _).symm
      _ = yonedaEquiv (b ≫ g i) := by rw [Category.assoc, hd i]
  have hext : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : P ⟶ Gl),
      (∀ (W : BigFppfOver B S hS) (y : P.obj (op W)), a.app (op W) y = b.app (op W) y) →
        a = b := fun a b h ↦ by
    refine NatTrans.ext (funext fun W ↦ ?_)
    obtain ⟨W⟩ := W
    apply ConcreteCategory.ext
    ext y
    exact h W y
  let η : F.left ⟶ Gl :=
    { app := fun W ↦ TypeCat.ofHom (sect W.unop)
      naturality := by
        intro W₁ W₂ q
        apply ConcreteCategory.ext
        ext y
        show sect W₂.unop (F.left.map q y) = Gl.map q (sect W₁.unop y)
        have hsymm : yonedaEquiv.symm (F.left.map q y) =
            yoneda.map q.unop ≫ yonedaEquiv.symm y := by
          apply yonedaEquiv.injective
          simpa using yonedaEquiv_naturality (yonedaEquiv.symm y) q.unop
        refine (sect_uniq W₂.unop (F.left.map q y) (Gl.map q (sect W₁.unop y)) ?_).symm
        intro W'' r i b hb
        have hfactor : b ≫ pullback.fst F.hom (f i) =
            yoneda.map (r ≫ q.unop) ≫ yonedaEquiv.symm y := by
          rw [hb, hsymm, yoneda.map_comp, Category.assoc]
        have hl := sect_spec W₁.unop y W'' (r ≫ q.unop) i b hfactor
        simpa only [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop] using hl }
  have hη : ∀ i, pullback.fst F.hom (f i) ≫ η = g i := by
    intro i
    refine hext _ _ fun W c ↦ ?_
    show sect W ((pullback.fst F.hom (f i)).app (op W) c) = (g i).app (op W) c
    have hb : yonedaEquiv.symm c ≫ pullback.fst F.hom (f i) =
        yonedaEquiv.symm ((pullback.fst F.hom (f i)).app (op W) c) := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      simp
    have hl := sect_spec W ((pullback.fst F.hom (f i)).app (op W) c) W (𝟙 W) i
      (yonedaEquiv.symm c) (by simpa using hb)
    have hglocal : yonedaEquiv (yonedaEquiv.symm c ≫ g i) = (g i).app (op W) c := by
      simpa using yonedaEquiv_comp (yonedaEquiv.symm c) (g i)
    simpa using hl.trans hglocal
  refine ⟨η, hη, ?_⟩
  intro d hd
  refine hext _ _ fun W y ↦ ?_
  exact sect_uniq W y (d.app (op W) y) fun W' k i b hb ↦ key d hd W W' y k i b hb

end Descend

/-! ### Independence of the local description of a morphism of descent data -/

variable (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- The move operation of a family transport is recovered from its gluing isomorphism by
lifting to the pairwise product and taking the second projection. -/
private lemma move_eq_lift_gluing {C : Type*} [Category C] [HasBinaryProducts C] {I : Type*}
    {A Bb : I → C} {p : ∀ i, A i ⟶ Bb i} (t : FamilyTransport A Bb p) {i j : I} {Z : C}
    (v : Z ⟶ A i) (y : Z ⟶ Bb j) :
    prod.lift v y ≫ (t.gluing i j).hom.left ≫ prod.snd = t.move v y := by
  rw [FamilyTransport.gluing_hom, prod.lift_snd, t.comp_move, prod.lift_fst, prod.lift_snd]

/-- The move operation of the descent datum of a sheaf over `T` is the move operation of its
fibre products. -/
private lemma transport_move_fibre (F : SheavesWithSpaceFibres f) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj ((fibreDescentData f hT hX F).obj i))
    (y : Z ⟶ Over.mk (f j)) :
    (fibreDescentData f hT hX F).transport.move v y = fibreMove f F.obj v y :=
  (DescentData.transport_move _ v y).trans (move_eq_lift_gluing (fibreTransport f F.obj) v y)

/-- A morphism of the descent data attached to two sheaves over `T` commutes with the move
operation on the fibre products. -/
private lemma fibreMove_descentHom {F G : SheavesWithSpaceFibres f}
    (φ : fibreDescentData f hT hX F ⟶ fibreDescentData f hT hX G) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F.obj i)) (y : Z ⟶ Over.mk (f j)) :
    fibreMove f F.obj v y ≫ (Over.map (f j)).map (φ.hom j) =
      fibreMove f G.obj (v ≫ (Over.map (f i)).map (φ.hom i)) y :=
  (congrArg (fun z ↦ z ≫ (Over.map (f j)).map (φ.hom j))
    (transport_move_fibre f hT hX F v y).symm).trans
      ((DescentData.move_naturality φ v y).trans (transport_move_fibre f hT hX G
        (v ≫ (Over.map (f i)).map (φ.hom i)) y))

/-- Two points of the fibre products with the same image in the sheaf have the same image in
the target sheaf under a morphism of descent data. This is the compatibility that makes the
components of a morphism of descent data descend to a morphism of sheaves. -/
private lemma descentHom_comp_fst_eq {F G : SheavesWithSpaceFibres f}
    (φ : fibreDescentData f hT hX F ⟶ fibreDescentData f hT hX G)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i j : ι}
    (a : Q ⟶ pullback F.obj.hom (f i)) (b : Q ⟶ pullback F.obj.hom (f j))
    (hab : a ≫ pullback.fst F.obj.hom (f i) = b ≫ pullback.fst F.obj.hom (f j)) :
    a ≫ (φ.hom i).left ≫ pullback.fst G.obj.hom (f i) =
      b ≫ (φ.hom j).left ≫ pullback.fst G.obj.hom (f j) := by
  have hcond : ∀ k : ι, pullback.fst F.obj.hom (f k) ≫ F.obj.hom =
      pullback.snd F.obj.hom (f k) ≫ f k := fun k ↦ pullback.condition
  let Z : Over T := Over.mk (a ≫ pullback.fst F.obj.hom (f i) ≫ F.obj.hom)
  have hv : a ≫ (pullback.snd F.obj.hom (f i) ≫ f i) = Z.hom := by
    simp only [Z, Over.mk_hom, ← hcond i]
  have hy : (b ≫ pullback.snd F.obj.hom (f j)) ≫ f j = Z.hom := by
    rw [Category.assoc, ← hcond j, ← Category.assoc, ← hab]
    simp only [Z, Over.mk_hom, Category.assoc]
  let v : Z ⟶ (Over.map (f i)).obj (fibreComponent f F.obj i) := Over.homMk a hv
  let yy : Z ⟶ Over.mk (f j) := Over.homMk (b ≫ pullback.snd F.obj.hom (f j)) hy
  have hmove : (fibreMove f F.obj v yy).left = b := by
    apply pullback.hom_ext
    · rw [fibreMove_left_fst]
      simpa [v] using hab
    · simp [yy]
  have key := congrArg (fun m ↦ m.left ≫ pullback.fst G.obj.hom (f j))
    (fibreMove_descentHom f hT hX φ v yy)
  simp only [Over.comp_left, Category.assoc, hmove, fibreMove_left_fst] at key
  exact key.symm

/-! ### Full faithfulness of the functor from sheaves to descent data -/

/-- **Fppf descent of morphisms of sheaves over `T`.** For an fppf covering `X i ⟶ T` of
algebraic spaces, every morphism between the descent data attached to two sheaves over `T`
whose fibre products with the covering are algebraic spaces comes from a unique morphism of
those sheaves. -/
public theorem existsUnique_hom_map_fibreDescentFunctor
    (hcov : Space.IsFppfCovering B S hS X f) {F G : SheavesWithSpaceFibres f}
    (φ : fibreDescentData f hT hX F ⟶ fibreDescentData f hT hX G) :
    ∃! ψ : F ⟶ G, (fibreDescentFunctor f hT hX).map ψ = φ := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ∀ i, pullback F.obj.hom (f i) ⟶ pullback G.obj.hom (f i),
      ∀ i, c i = (φ.hom i).left := ⟨fun i ↦ (φ.hom i).left, fun _ ↦ rfl⟩
  have hw : ∀ i, c i ≫ pullback.snd G.obj.hom (f i) = pullback.snd F.obj.hom (f i) := by
    intro i
    rw [hc i]
    exact Over.w (φ.hom i)
  have hcf : ∀ i, c i ≫ pullback.fst G.obj.hom (f i) =
      (φ.hom i).left ≫ pullback.fst G.obj.hom (f i) := fun i ↦ by rw [hc i]; rfl
  have hg : FibreCompatible f F.obj (fun i ↦ c i ≫ pullback.fst G.obj.hom (f i)) := by
    intro Q i j a b hab
    show a ≫ c i ≫ pullback.fst G.obj.hom (f i) = b ≫ c j ≫ pullback.fst G.obj.hom (f j)
    rw [hc i, hc j]
    exact descentHom_comp_fst_eq f hT hX φ a b hab
  obtain ⟨d, hd, hdu⟩ := existsUnique_desc_of_fibreCompatible f F.obj hcov G.property.1
    (fun i ↦ c i ≫ pullback.fst G.obj.hom (f i)) hg
  have hbase : ∀ i, pullback.fst F.obj.hom (f i) ≫ d ≫ G.obj.hom =
      pullback.fst F.obj.hom (f i) ≫ F.obj.hom := by
    intro i
    have hcG : pullback.fst G.obj.hom (f i) ≫ G.obj.hom =
        pullback.snd G.obj.hom (f i) ≫ f i := pullback.condition
    have hcF : pullback.fst F.obj.hom (f i) ≫ F.obj.hom =
        pullback.snd F.obj.hom (f i) ≫ f i := pullback.condition
    rw [← Category.assoc, hd i, Category.assoc, hcG, ← Category.assoc, hw i, hcF]
  have hdT : d ≫ G.obj.hom = F.obj.hom := by
    have hgT : FibreCompatible f F.obj
        (fun i ↦ pullback.fst F.obj.hom (f i) ≫ F.obj.hom) := by
      intro Q i j a b hab
      rw [← Category.assoc, ← Category.assoc, hab]
    obtain ⟨e, _, heu⟩ := existsUnique_desc_of_fibreCompatible f F.obj hcov hT.isSheaf
      (fun i ↦ pullback.fst F.obj.hom (f i) ≫ F.obj.hom) hgT
    exact (heu (d ≫ G.obj.hom) hbase).trans (heu F.obj.hom fun _ ↦ rfl).symm
  refine ⟨ObjectProperty.homMk (Over.homMk d hdT), ?_, ?_⟩
  · refine DescentData.Hom.ext (funext fun i ↦ ?_)
    show fibreComponentMap f (Over.homMk d hdT) i = φ.hom i
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [fibreComponentMap_left_fst]
      exact (hd i).trans (hcf i)
    · rw [fibreComponentMap_left_snd]
      exact (Over.w (φ.hom i)).symm
  · intro ψ hψ
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    refine hdu ψ.hom.left fun i ↦ ?_
    have h1 : fibreComponentMap f ψ.hom i = φ.hom i :=
      congrFun (congrArg DescentData.Hom.hom hψ) i
    have h2 : pullback.fst F.obj.hom (f i) ≫ ψ.hom.left =
        (φ.hom i).left ≫ pullback.fst G.obj.hom (f i) :=
      (fibreComponentMap_left_fst f ψ.hom i).symm.trans
        (congrArg (fun m : fibreComponent f F.obj i ⟶ fibreComponent f G.obj i ↦
          m.left ≫ pullback.fst G.obj.hom (f i)) h1)
    exact h2.trans (hcf i).symm

/-- **Stacks 0ADT**, half of the asserted equivalence: for an fppf covering of algebraic
spaces, the functor from sheaves over the target whose fibre products with the covering are
algebraic spaces to descent data relative to the covering is fully faithful. -/
@[stacks 0ADT "FULL FAITHFULNESS of the right-to-left functor of the asserted \
equivalence, for an fppf covering of algebraic spaces. The other half, essential surjectivity via \
the coequalizer, is NOT proved, so the equivalence is not claimed"]
public def fibreDescentFunctorFullyFaithful (hcov : Space.IsFppfCovering B S hS X f) :
    (fibreDescentFunctor f hT hX).FullyFaithful where
  preimage φ := (existsUnique_hom_map_fibreDescentFunctor f hT hX hcov φ).choose
  map_preimage φ :=
    (existsUnique_hom_map_fibreDescentFunctor f hT hX hcov φ).choose_spec.1
  preimage_map ψ :=
    ((existsUnique_hom_map_fibreDescentFunctor f hT hX hcov
      ((fibreDescentFunctor f hT hX).map ψ)).choose_spec.2 ψ rfl).symm

/-! ### The descent datum of an algebraic space over `T` is the canonical one -/

section Canonical

variable (U : AlgebraicSpacesOver (B := B) (S := S) (hS := hS) T)

/-- The trivial descent datum of an algebraic space over `T`. -/
public abbrev trivDatum : HomDescentData.{u, v} (𝟙 T) hT hT :=
  (trivialDescentFunctor.{u, v} T hT).obj U

/-- The canonical descent datum of an algebraic space over `T`, with its component pullback
squares and the base change of its gluing isomorphisms. -/
public abbrev canDatum :
    PulledBackDatum (fun _ : PUnit.{v + 1} ↦ 𝟙 T) f hT (fun _ ↦ hT) hT hX
      (fun _ ↦ PUnit.unit) f (trivDatum.{u, v} hT U) :=
  pullbackDatum (fun _ : PUnit.{v + 1} ↦ 𝟙 T) f hT (fun _ ↦ hT) hT hX
    (fun _ ↦ PUnit.unit) f (trivDatum.{u, v} hT U) (𝟙 T) (by simp)

/-- The canonical descent datum is the pulled-back datum. -/
public lemma familyCanonical_obj_eq :
    (familyCanonicalDescentFunctor f hT hX).obj U = (canDatum f hT hX U).datum :=
  (pullbackFunctor (fun _ : PUnit.{v + 1} ↦ 𝟙 T) f hT (fun _ ↦ hT) hT hX
    (fun _ ↦ PUnit.unit) (𝟙 T) f (by simp)).obj_eq (trivDatum.{u, v} hT U)

/-- The component of the canonical descent datum at `i` is the fibre product `X i ×_T U`. -/
public def canComponentIso (i : ι) :
    (canDatum f hT hX U).datum.obj i ≅ fibreComponent f U.obj i :=
  Over.isoMk
    (((canDatum f hT hX U).obj_isPullback i).isoIsPullback _ _
      (IsPullback.of_hasPullback U.obj.hom (f i)).flip) (by simp)

/-- The isomorphism of components carries the projection of the canonical datum to the
projection of the fibre product. -/
private lemma canComponentIso_hom_left_fst (i : ι) :
    (canComponentIso f hT hX U i).hom.left ≫ pullback.fst U.obj.hom (f i) =
      (canDatum f hT hX U).objMap i :=
  IsPullback.isoIsPullback_hom_snd _ _ ((canDatum f hT hX U).obj_isPullback i)
    (IsPullback.of_hasPullback U.obj.hom (f i)).flip

/-- The gluing isomorphism of the canonical descent datum preserves the projection to the
descended space. -/
private lemma canDatum_gluing_objMap (i j : ι) :
    ((canDatum f hT hX U).datum.gluing i j).hom.left.left ≫
        (prod.snd : Over.mk (f i) ⨯
          (Over.map (f j)).obj ((canDatum f hT hX U).datum.obj j) ⟶ _).left ≫
          (canDatum f hT hX U).objMap j =
      (prod.fst : (Over.map (f i)).obj ((canDatum f hT hX U).datum.obj i) ⨯
          Over.mk (f j) ⟶ _).left ≫ (canDatum f hT hX U).objMap i := by
  have h := (canDatum f hT hX U).gluing_comm i j
  have h2 := congrArg (fun m ↦ m ≫ (prod.snd : Over.mk (𝟙 T) ⨯
    (Over.map (𝟙 T)).obj ((trivDatum.{u, v} hT U).obj PUnit.unit) ⟶ _).left) h
  simp only [Category.assoc] at h2
  have hbr : ((trivDatum.{u, v} hT U).gluing PUnit.unit PUnit.unit).hom.left.left ≫
        (prod.snd : Over.mk (𝟙 T) ⨯
          (Over.map (𝟙 T)).obj ((trivDatum.{u, v} hT U).obj PUnit.unit) ⟶ _).left =
      (prod.fst : (Over.map (𝟙 T)).obj ((trivDatum.{u, v} hT U).obj PUnit.unit) ⨯
        Over.mk (𝟙 T) ⟶ _).left :=
    congrArg Over.Hom.left (prod.lift_snd _ _)
  rw [← (canDatum f hT hX U).gluingTarget_snd, ← (canDatum f hT hX U).gluingSource_fst, ← hbr]
  exact h2.symm

/-- The isomorphisms of components commute with the move operations of the two descent
data. -/
private lemma canComponentIso_move {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj ((canDatum f hT hX U).datum.obj i))
    (y : Z ⟶ Over.mk (f j)) :
    (canDatum f hT hX U).datum.transport.move v y ≫
        (Over.map (f j)).map (canComponentIso f hT hX U j).hom =
      (fibreDescentData f hT hX
          ((algebraicSpacesOverToSheaves f hT hX).obj U)).transport.move
        (v ≫ (Over.map (f i)).map (canComponentIso f hT hX U i).hom) y := by
  have h2 : (fibreDescentData f hT hX
        ((algebraicSpacesOverToSheaves f hT hX).obj U)).transport.move
          (v ≫ (Over.map (f i)).map (canComponentIso f hT hX U i).hom) y =
      fibreMove f U.obj (v ≫ (Over.map (f i)).map (canComponentIso f hT hX U i).hom) y :=
    transport_move_fibre f hT hX _ _ y
  rw [DescentData.transport_move, h2]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.map_map_left, fibreMove_left_fst,
      canComponentIso_hom_left_fst, canDatum_gluing_objMap]
    rw [← Category.assoc, ← Over.comp_left, prod.lift_fst]
  · have hsnd : ((canDatum f hT hX U).datum.gluing i j).hom.left ≫
        prod.snd ≫ structureMap (f j) ((canDatum f hT hX U).datum.obj j) = prod.snd :=
      DescentData.gluing_hom_snd_structureMap _ i j
    have hw : (canComponentIso f hT hX U j).hom.left ≫ pullback.snd U.obj.hom (f j) =
        ((canDatum f hT hX U).datum.obj j).hom := Over.w (canComponentIso f hT hX U j).hom
    have key : prod.lift v y ≫ ((canDatum f hT hX U).datum.gluing i j).hom.left ≫
        prod.snd ≫ structureMap (f j) ((canDatum f hT hX U).datum.obj j) = y := by
      rw [hsnd, prod.lift_snd]
    simp only [Over.mk_left, Category.assoc, Over.comp_left, Over.map_obj_left,
      Over.map_map_left, fibreMove_left_snd, hw]
    exact congrArg Over.Hom.left key

/-- The isomorphisms of components are compatible with the gluing isomorphisms. -/
public lemma canComponentIso_comm (i j : ι) :
    prod.map ((Over.map (f i)).map (canComponentIso f hT hX U i).hom) (𝟙 (Over.mk (f j))) ≫
        ((fibreDescentData f hT hX
          ((algebraicSpacesOverToSheaves f hT hX).obj U)).gluing i j).hom.left =
      ((canDatum f hT hX U).datum.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i)))
          ((Over.map (f j)).map (canComponentIso f hT hX U j).hom) := by
  rw [← DescentData.transport_gluing (canDatum f hT hX U).datum i j,
    ← DescentData.transport_gluing
      (fibreDescentData f hT hX ((algebraicSpacesOverToSheaves f hT hX).obj U)) i j]
  exact FamilyTransport.gluing_comm (canDatum f hT hX U).datum.transport
    (fibreDescentData f hT hX ((algebraicSpacesOverToSheaves f hT hX).obj U)).transport
    (fun k ↦ (Over.map (f k)).map (canComponentIso f hT hX U k).hom)
    (fun k ↦ structureMap_naturality (f k) (canComponentIso f hT hX U k).hom)
    (fun v y ↦ canComponentIso_move f hT hX U v y) i j

/-- **Stacks 0ADT**, the identification behind part (2): the canonical descent datum of an
algebraic space over `T` is the descent datum of that space read as a sheaf over `T`. -/
public def canonicalIsoFibreDescentData :
    (familyCanonicalDescentFunctor f hT hX).obj U ≅
      fibreDescentData f hT hX ((algebraicSpacesOverToSheaves f hT hX).obj U) :=
  eqToIso (familyCanonical_obj_eq f hT hX U) ≪≫
    DescentData.isoMk (canComponentIso f hT hX U) (canComponentIso_comm f hT hX U)

end Canonical

/-! ### Part (2): algebraicity versus effectivity -/

/-- The descent datum of an algebraic space over `T`, read as a sheaf over `T`, is
effective. -/
public theorem isEffective_fibreDescentData_of_isAlgebraicSpace
    (F : SheavesWithSpaceFibres f) (hF : IsAlgebraicSpace B S hS F.obj.left) :
    DescentData.IsEffective (fibreDescentData f hT hX F) :=
  ⟨⟨F.obj, hF⟩, ⟨canonicalIsoFibreDescentData f hT hX ⟨F.obj, hF⟩⟩⟩

/-- **Stacks 0ADT, part (2).** For an fppf covering of algebraic spaces, a sheaf over the
target whose fibre products with the covering are algebraic spaces is itself an algebraic
space exactly when its descent datum is effective. -/
@[stacks 0ADT "PART (2) IN FULL: the sheaf F is an algebraic space if and only if the \
corresponding descent datum is effective, against this library's DescentData.IsEffective. Proved \
WITHOUT Stacks 0ADV -- effectivity hands over an algebraic space and full faithfulness transports \
the isomorphism back. The equivalence of categories itself is NOT here: essential surjectivity, \
i.e. the left-to-right coequalizer functor, is unproved"]
public theorem isAlgebraicSpace_iff_isEffective_fibreDescentData
    (hcov : Space.IsFppfCovering B S hS X f) (F : SheavesWithSpaceFibres f) :
    IsAlgebraicSpace B S hS F.obj.left ↔
      DescentData.IsEffective (fibreDescentData f hT hX F) := by
  refine ⟨isEffective_fibreDescentData_of_isAlgebraicSpace f hT hX F, ?_⟩
  rintro ⟨U, ⟨e⟩⟩
  have e' : (fibreDescentFunctor f hT hX).obj ((algebraicSpacesOverToSheaves f hT hX).obj U) ≅
      (fibreDescentFunctor f hT hX).obj F :=
    (canonicalIsoFibreDescentData f hT hX U).symm ≪≫ e
  have e'' : (algebraicSpacesOverToSheaves f hT hX).obj U ≅ F :=
    (fibreDescentFunctorFullyFaithful f hT hX hcov).preimageIso e'
  exact U.property.of_iso (Over.forget T |>.mapIso ((ObjectProperty.ι _).mapIso e''))

end AlgebraicGeometry.Space.Descent

end
