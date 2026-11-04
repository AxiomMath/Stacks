module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A colimit of separated algebraic spaces is a colimit among all algebraic spaces

Let `B` be an algebraic space over a scheme `S` and let `i ↦ X i` be a diagram of algebraic
spaces separated over `B`. Suppose that the diagram has a colimit `X` in the category of
algebraic spaces separated over `B`, that the `X i` jointly cover `X`, that every separated
étale algebraic space over `X` is the colimit of its base changes to the `X i`, and that every
compatible family of separated étale algebraic spaces over the `X i` is the family of base
changes of a separated étale algebraic space over `X`. Then `X` is the colimit of the diagram
in the category of *all* algebraic spaces over `B`.

## Main definitions

* `AlgebraicGeometry.Space.SeparatedOver` is the category of algebraic spaces separated over a
  fixed algebraic space `B`: the full subcategory of the algebraic spaces over `B` on the
  objects whose structure morphism is separated.
* `AlgebraicGeometry.Space.separatedOverInclusion` is its inclusion into the algebraic spaces
  over `B`.
* `AlgebraicGeometry.Space.IsEtaleSeparated` says that a morphism of algebraic spaces separated
  over `B` is étale and separated.

## Main results

* `AlgebraicGeometry.Space.isColimit_of_separated_etale_descent`: **Stacks 0GFP**, the cocone
  is a colimit in the category of algebraic spaces over `B`.

## Implementation notes

The five hypotheses of the source are encoded as follows.

1. *Each `X i` is separated over `B`.* This is carried by the shape of the diagram: it is a
   functor into `AlgebraicGeometry.Space.SeparatedOver`, whose objects are by definition the
   algebraic spaces with separated structure morphism to `B`.
2. *`X = colim X i` exists in the category of algebraic spaces separated over `B`.* This is the
   cocone `c` together with `hc : IsColimit c`, both in `SeparatedOver`.
3. *`∐ X i → X` is surjective.* Stated on points: every point of `X` is the image of a point of
   some `X i`. Surjectivity of a morphism of algebraic spaces is by definition (Tag 03ME)
   surjectivity of the induced map on points, and a point of `∐ X i` is a point of some `X i`,
   so this is the same condition; stating it this way avoids choosing a coproduct.
4. *If `U → X` is a separated étale morphism and `U i = X i ×_X U`, then `U = colim U i` in the
   algebraic spaces separated over `B`.* Stated as `hbase`: a cocone `d` on a diagram `E` over
   the diagram `D`, whose vertex carries a separated étale morphism `q` to `X` and all of whose
   comparison squares are cartesian, is a colimit. Cartesianness of those squares says exactly
   that `E i = X i ×_X U` compatibly with the transition morphisms.
5. *Every object `(U i → X i)` of `lim X i ,spaces,étale` with `U i → X i` separated is of the
   form `U i = X i ×_X U` for a separated étale morphism of algebraic spaces `U → X`.* Stated
   as `hdesc`: an object of the limit of the small étale sites of the `X i` is a diagram `E`
   with a natural transformation `p` to `D` which is étale in each component and whose
   transition squares are cartesian; the conclusion produces a cocone `d` on `E` together with
   a separated étale morphism `q` from its vertex to `X` making all the comparison squares
   cartesian. Separatedness of `E i` over `B` is not an extra assumption: it follows from
   separatedness of `p.app i` and of `X i` over `B`.

The conclusion is that the image of `c` under the inclusion of the separated algebraic spaces
over `B` into all algebraic spaces over `B` is a colimit, i.e. `X = colim X i` in the category
of all algebraic spaces over `B`.

## References

* [Stacks Project, Tag 0GFP](https://stacks.math.columbia.edu/tag/0GFP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

variable (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)

/-! ### Algebraic spaces separated over a base -/

/-- The category of algebraic spaces separated over `B`: the full subcategory of the algebraic
spaces over `B` on the objects whose structure morphism is separated. -/
abbrev SeparatedOver (B : AlgebraicSpaces site S hS) :=
  ObjectProperty.FullSubcategory (fun X : Over B => IsSeparated site S hS X.hom.hom)

/-- The inclusion of the algebraic spaces separated over `B` into the algebraic spaces
over `B`. -/
abbrev separatedOverInclusion (B : AlgebraicSpaces site S hS) :
    SeparatedOver site S hS B ⥤ Over B :=
  ObjectProperty.ι _

/-- A morphism of algebraic spaces separated over `B` which is étale and separated. -/
abbrev IsEtaleSeparated {B : AlgebraicSpaces site S hS} {U X : SeparatedOver site S hS B}
    (f : U ⟶ X) : Prop :=
  IsEtale site S hS f.hom.left.hom ∧ IsSeparated site S hS f.hom.left.hom

variable {site S hS}

/-! ### Separatedness bookkeeping -/

/-- A composition of separated morphisms of algebraic spaces is separated. -/
private theorem separated_comp {X Y Z : AlgebraicSpaces site S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSeparated site S hS f.hom) (hg : IsSeparated site S hS g.hom) :
    IsSeparated site S hS (f ≫ g).hom :=
  isSeparated_comp site S hS f.hom g.hom hf hg

/-- A base change of a separated morphism of algebraic spaces is separated. -/
private theorem separated_of_isPullback {P X Y Z : AlgebraicSpaces site S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hf : IsSeparated site S hS f.hom) :
    IsSeparated site S hS b.hom := by
  have sq' : IsPullback a.hom b.hom f.hom g.hom := AlgebraicSpaces.isPullback_hom _ _ _ sq
  have hsnd := sq'.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f.hom g.hom)
  rw [← hsnd]
  exact isSeparated_comp site S hS _ _
    (isSeparated_of_isIso site S hS
      (sq'.isoIsPullback _ _ (IsPullback.of_hasPullback f.hom g.hom)).hom)
    (isSeparated_pullback site S hS f.hom g.hom hf)

/-- Any morphism out of an algebraic space separated over `B` is separated. -/
private theorem separated_of_source {B : AlgebraicSpaces site S hS}
    (X : SeparatedOver site S hS B) {Z : Over B} (f : X.obj ⟶ Z) :
    IsSeparated site S hS f.left.hom := by
  apply isSeparated_of_comp site S hS f.left.hom Z.hom.hom
  rw [show f.left.hom ≫ Z.hom.hom = X.obj.hom.hom from congrArg (fun k => k.hom) (Over.w f)]
  exact X.property

/-! ### Fibre products in the separated algebraic spaces over `B` -/

/-- The fibre product of two morphisms of algebraic spaces separated over `B` with a common
target, taken in the algebraic spaces over `B`, is separated over `B`. -/
private noncomputable abbrev separatedPullback {B : AlgebraicSpaces site S hS}
    {X Y : SeparatedOver site S hS B} {Z : Over B} (f : X.obj ⟶ Z) (g : Y.obj ⟶ Z) :
    SeparatedOver site S hS B :=
  ⟨Over.mk (pullback.fst f.left g.left ≫ X.obj.hom),
    separated_comp _ _
      (separated_of_isPullback (IsPullback.of_hasPullback f.left g.left).flip
        (separated_of_source Y g)) X.property⟩

/-- The first projection of the fibre product of separated algebraic spaces over `B`. -/
private noncomputable abbrev separatedPullbackFst {B : AlgebraicSpaces site S hS}
    {X Y : SeparatedOver site S hS B} {Z : Over B} (f : X.obj ⟶ Z) (g : Y.obj ⟶ Z) :
    separatedPullback f g ⟶ X :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.left g.left) rfl)

/-- The second projection of the fibre product of separated algebraic spaces over `B`. -/
private noncomputable abbrev separatedPullbackSnd {B : AlgebraicSpaces site S hS}
    {X Y : SeparatedOver site S hS B} {Z : Over B} (f : X.obj ⟶ Z) (g : Y.obj ⟶ Z) :
    separatedPullback f g ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f.left g.left) (by
    change pullback.snd f.left g.left ≫ Y.obj.hom =
      pullback.fst f.left g.left ≫ X.obj.hom
    rw [← Over.w g, ← Over.w f, ← Category.assoc, ← Category.assoc,
      pullback.condition]))

/-- The morphism into the fibre product of separated algebraic spaces over `B` induced by a
pair of morphisms agreeing on the common target. -/
private noncomputable abbrev separatedPullbackLift {B : AlgebraicSpaces site S hS}
    {X Y T : SeparatedOver site S hS B} {Z : Over B} {f : X.obj ⟶ Z} {g : Y.obj ⟶ Z}
    (a : T ⟶ X) (b : T ⟶ Y) (h : a.hom ≫ f = b.hom ≫ g) :
    T ⟶ separatedPullback f g :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift a.hom.left b.hom.left (congrArg Over.Hom.left h)) (by
      change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ X.obj.hom) = T.obj.hom
      rw [← Category.assoc, pullback.lift_fst, Over.w]))

/-- Two morphisms of algebraic spaces separated over `B` are equal if their underlying morphisms
of algebraic spaces are. -/
private theorem separatedOver_hom_ext {B : AlgebraicSpaces site S hS}
    {X Y : SeparatedOver site S hS B} {a b : X ⟶ Y} (h : a.hom.left = b.hom.left) : a = b :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-- The induced morphism into a fibre product of separated algebraic spaces over `B` recovers
the first of the two given morphisms. -/
private theorem separatedPullbackLift_fst {B : AlgebraicSpaces site S hS}
    {X Y T : SeparatedOver site S hS B} {Z : Over B} {f : X.obj ⟶ Z} {g : Y.obj ⟶ Z}
    (a : T ⟶ X) (b : T ⟶ Y) (h : a.hom ≫ f = b.hom ≫ g) :
    separatedPullbackLift a b h ≫ separatedPullbackFst f g = a :=
  separatedOver_hom_ext (pullback.lift_fst _ _ _)

/-- The induced morphism into a fibre product of separated algebraic spaces over `B` recovers
the second of the two given morphisms. -/
private theorem separatedPullbackLift_snd {B : AlgebraicSpaces site S hS}
    {X Y T : SeparatedOver site S hS B} {Z : Over B} {f : X.obj ⟶ Z} {g : Y.obj ⟶ Z}
    (a : T ⟶ X) (b : T ⟶ Y) (h : a.hom ≫ f = b.hom ≫ g) :
    separatedPullbackLift a b h ≫ separatedPullbackSnd f g = b :=
  separatedOver_hom_ext (pullback.lift_snd _ _ _)

/-- Two morphisms into a fibre product of separated algebraic spaces over `B` agreeing on both
projections are equal. -/
private theorem separatedPullback_hom_ext {B : AlgebraicSpaces site S hS}
    {X Y T : SeparatedOver site S hS B} {Z : Over B} {f : X.obj ⟶ Z} {g : Y.obj ⟶ Z}
    {a b : T ⟶ separatedPullback f g}
    (h₁ : a ≫ separatedPullbackFst f g = b ≫ separatedPullbackFst f g)
    (h₂ : a ≫ separatedPullbackSnd f g = b ≫ separatedPullbackSnd f g) : a = b := by
  apply separatedOver_hom_ext
  apply pullback.hom_ext
  · exact congrArg (fun k => k.hom.left) h₁
  · exact congrArg (fun k => k.hom.left) h₂

/-- Two morphisms out of the vertex of a colimit of separated algebraic spaces over `B` which
agree on the legs of the cocone are equal, even when the target is an arbitrary algebraic space
over `B`: their equalizer is the fibre product, which the colimit factors through. -/
private theorem hom_ext_of_separated_colimit {B : AlgebraicSpaces site S hS}
    {I : Type v} [Category.{w} I] {D : I ⥤ SeparatedOver site S hS B} {c : Cocone D}
    (hc : IsColimit c) {Z : Over B} {f g : c.pt.obj ⟶ Z}
    (h : ∀ i, (c.ι.app i).hom ≫ f = (c.ι.app i).hom ≫ g) : f = g := by
  let d : Cocone D :=
    { pt := separatedPullback f g
      ι :=
        { app := fun i => separatedPullbackLift (c.ι.app i) (c.ι.app i) (h i)
          naturality := by
            intro i j k
            show D.map k ≫ separatedPullbackLift (c.ι.app j) (c.ι.app j) (h j) =
              separatedPullbackLift (c.ι.app i) (c.ι.app i) (h i) ≫ 𝟙 _
            apply Eq.trans _ (Category.comp_id _).symm
            apply separatedPullback_hom_ext
            all_goals simp only [Category.assoc, separatedPullbackLift_fst,
              separatedPullbackLift_snd, c.w] } }
  have h₁₂ : hc.desc d ≫ separatedPullbackFst f g = 𝟙 c.pt ∧
      hc.desc d ≫ separatedPullbackSnd f g = 𝟙 c.pt := by
    constructor <;> refine hc.hom_ext fun i => ?_ <;>
      rw [← Category.assoc, hc.fac, Category.comp_id] <;>
      first
        | exact separatedPullbackLift_fst (c.ι.app i) (c.ι.app i) (h i)
        | exact separatedPullbackLift_snd (c.ι.app i) (c.ι.app i) (h i)
  have hw : (separatedPullbackFst f g).hom ≫ f = (separatedPullbackSnd f g).hom ≫ g :=
    Over.OverMorphism.ext pullback.condition
  simpa only [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    h₁₂.1, h₁₂.2, ObjectProperty.FullSubcategory.id_hom, Category.id_comp] using
    congrArg (fun k => (hc.desc d).hom ≫ k) hw

/-! ### Points and surjectivity -/

/-- A morphism of algebraic spaces is surjective as soon as it receives a family of surjective
morphisms whose targets cover its target on points. -/
private theorem surjective_of_commuting_jointly_surjective_family
    {I : Type v} {X Y : AlgebraicSpaces site S hS} (q : Y ⟶ X)
    (A E : I → AlgebraicSpaces site S hS)
    (cc : ∀ i, A i ⟶ X) (d : ∀ i, E i ⟶ Y) (p : ∀ i, E i ⟶ A i)
    (hcover : ∀ x : points site S hS X.obj,
      ∃ i : I, ∃ y : points site S hS (A i).obj,
        pointsMap site S hS (A i).obj (cc i).hom y = x)
    (hp : ∀ i, IsSurjective site S hS (p i).hom)
    (hcomm : ∀ i, d i ≫ q = p i ≫ cc i) :
    IsSurjective site S hS q.hom := by
  intro x
  obtain ⟨i, y, hy⟩ := hcover x
  obtain ⟨z, hz⟩ := hp i y
  refine ⟨pointsMap site S hS (E i).obj (d i).hom z, ?_⟩
  calc
    _ = pointsMap site S hS (E i).obj ((d i).hom ≫ q.hom) z :=
        (pointsMap_comp_apply site S hS (d i).hom q.hom z).symm
    _ = pointsMap site S hS (E i).obj ((p i).hom ≫ (cc i).hom) z := by
        rw [← ObjectProperty.FullSubcategory.comp_hom,
          ← ObjectProperty.FullSubcategory.comp_hom, hcomm i]
    _ = pointsMap site S hS (A i).obj (cc i).hom
        (pointsMap site S hS (E i).obj (p i).hom z) :=
        pointsMap_comp_apply site S hS (p i).hom (cc i).hom z
    _ = x := by rw [hz, hy]

/-! ### Descent along a surjective étale morphism -/

/-- A morphism out of the source of a surjective étale morphism of algebraic spaces which does
not distinguish the two projections of its fibre square descends uniquely to the target: a
surjective étale morphism is an fpqc covering, and an algebraic space is an fpqc sheaf. -/
private theorem existsUnique_desc_of_etale_surjective
    {U X : AlgebraicSpaces site S hS} (q : U ⟶ X)
    (he : IsEtale site S hS q.hom) (hs : IsSurjective site S hS q.hom)
    {Z : AlgebraicSpaces site S hS} (g : U ⟶ Z)
    (hg : ∀ (T : AlgebraicSpaces site S hS) (a b : T ⟶ U),
      a ≫ q = b ≫ q → a ≫ g = b ≫ g) :
    ∃! f : X ⟶ Z, q ≫ f = g := by
  have hcov : IsEtaleCovering site S hS (fun _ : Unit => U.obj) (fun _ => q.hom) :=
    { target_isAlgebraicSpace := X.property
      source_isAlgebraicSpace := fun _ => U.property
      etale := fun _ => he
      jointly_surjective := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
        obtain ⟨y, hy⟩ := hs x
        exact ⟨(), y, hy⟩ }
  obtain ⟨f, hf, hu⟩ := existsUnique_desc_of_fpqcCovering site S hS (fun _ : Unit => q)
    (isFpqcCovering_of_isEtaleCovering site S hS _ _ hcov) Z (fun _ => g)
    (fun _ _ => hg _ _ _ (AlgebraicSpaces.isPullback_fiberProduct site S hS q q).w)
  exact ⟨f, hf (), fun f' hf' => hu f' (fun _ => hf')⟩

/-- Two morphisms out of the target of a surjective étale morphism of algebraic spaces which
agree after composing with it are equal. -/
private theorem etale_surjective_hom_ext
    {U X : AlgebraicSpaces site S hS} (q : U ⟶ X)
    (he : IsEtale site S hS q.hom) (hs : IsSurjective site S hS q.hom)
    {Z : AlgebraicSpaces site S hS} {f g : X ⟶ Z} (h : q ≫ f = q ≫ g) : f = g := by
  obtain ⟨_k, _hk, hu⟩ := existsUnique_desc_of_etale_surjective q he hs (q ≫ f)
    (fun T a b hab => by rw [← Category.assoc, ← Category.assoc, hab])
  exact (hu f rfl).trans (hu g h.symm).symm

/-- Two morphisms out of the source of a cartesian square which agree after composing with the
morphism being base changed agree already, provided the comparison morphism identifies them. -/
private theorem pullback_hom_agree {C : Type*} [Category C] {E X U V Z T : C}
    {p : E ⟶ X} {k : E ⟶ U} {cc : X ⟶ V} {q : U ⟶ V}
    (sq : IsPullback p k cc q) {g : U ⟶ Z} {f : X ⟶ Z}
    (h : k ≫ g = p ≫ f) (t : T ⟶ X) (a b : T ⟶ U)
    (ha : t ≫ cc = a ≫ q) (hb : t ≫ cc = b ≫ q) : a ≫ g = b ≫ g := by
  have key (x : T ⟶ U) (hx : t ≫ cc = x ≫ q) : x ≫ g = t ≫ f := by
    rw [← sq.lift_snd t x hx, Category.assoc, h, ← Category.assoc, sq.lift_fst]
  exact (key a ha).trans (key b hb).symm

/-! ### A separated étale chart which is separated over the base -/

/-- A morphism from a separated scheme of the site to an algebraic space is separated: it is
separated over the terminal object, hence separated. -/
private theorem isSeparated_map_from_separated_scheme
    {X : AlgebraicSpaces site S hS} (U : BigFppfOver site S hS)
    (hU : Scheme.IsSeparated ((BigFppfOver.toScheme site S hS).obj U))
    (f : yoneda.obj U ⟶ X.obj) :
    IsSeparated site S hS f := by
  let Tsch : BigFppfOver site S hS := Over.mk (𝟙 (site.obj hS))
  have hTsch : IsTerminal Tsch := IsTerminal.ofUniqueHom
    (fun V => Over.homMk V.hom rfl) (by
      intro V a
      apply Over.OverMorphism.ext
      show a.left = V.hom
      simpa [Tsch] using Over.w a)
  let Tsp : AlgebraicSpaces site S hS :=
    ⟨yoneda.obj Tsch, isAlgebraicSpace_yoneda site S hS Tsch⟩
  have hTyoneda : IsTerminal (yoneda.obj Tsch) := IsTerminal.isTerminalObj yoneda Tsch hTsch
  have hTsp : IsTerminal Tsp := IsTerminal.ofUniqueHom
    (fun Y => ObjectProperty.homMk (hTyoneda.from Y.obj)) (by
      intro Y g
      apply ObjectProperty.hom_ext
      exact hTyoneda.hom_ext _ _)
  let Usp : AlgebraicSpaces site S hS :=
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda site S hS U⟩
  let fsp : Usp ⟶ X := ObjectProperty.homMk f
  let toBase : U ⟶ Tsch := Over.homMk U.hom rfl
  have hcomp : IsSeparated site S hS (fsp.hom ≫ (hTsp.from X).hom) := by
    have heq : fsp.hom ≫ (hTsp.from X).hom = yoneda.map toBase := hTyoneda.hom_ext _ _
    rw [heq]
    have hUmap : _root_.AlgebraicGeometry.IsSeparated
        ((BigFppfOver.toScheme site S hS).map toBase) := by
      infer_instance
    exact (isSeparated_yoneda_map_iff site S hS toBase).2 hUmap
  exact isSeparated_of_comp site S hS fsp.hom (hTsp.from X).hom hcomp

/-- Every algebraic space over `B` admits a surjective étale morphism from an algebraic space
which is separated over `B`: take an étale surjective chart by a disjoint union of affines,
which is a separated scheme. -/
private theorem exists_separated_etale_cover {B : AlgebraicSpaces site S hS} (Z : Over B) :
    ∃ (W : SeparatedOver site S hS B) (f : W.obj ⟶ Z),
      IsEtale site S hS f.left.hom ∧ IsSurjective site S hS f.left.hom := by
  obtain ⟨U, f, J, Y, e, hs, he, ha, -⟩ :=
    exists_etale_surjective_coproduct_affine_cover site S hS Z.left.obj Z.left.property
  have _ (j : J) : IsAffine (Y j) := ha j
  let k := e.inv ≫ (Sigma.mapIso (fun j => Scheme.isoSpec (Y j))).hom ≫
    sigmaSpec (fun j => Scheme.Γ.obj (Opposite.op (Y j)))
  have hU : Scheme.IsSeparated ((BigFppfOver.toScheme site S hS).obj U) := by
    have hk : _root_.AlgebraicGeometry.IsSeparated k := by
      have hsig : _root_.AlgebraicGeometry.IsSeparated
          (sigmaSpec (fun j => Scheme.Γ.obj (Opposite.op (Y j)))) := inferInstance
      exact MorphismProperty.comp_mem
        (@_root_.AlgebraicGeometry.IsSeparated)
        (e.inv ≫ (Sigma.mapIso (fun j => Scheme.isoSpec (Y j))).hom)
        (sigmaSpec (fun j => Scheme.Γ.obj (Opposite.op (Y j))))
        (MorphismProperty.comp_mem (@_root_.AlgebraicGeometry.IsSeparated) e.inv
          (Sigma.mapIso (fun j => Scheme.isoSpec (Y j))).hom inferInstance inferInstance)
        hsig
    constructor
    rw [← terminal.comp_from k]
    infer_instance
  let W : AlgebraicSpaces site S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda site S hS U⟩
  let f' : W ⟶ Z.left := ObjectProperty.homMk f
  let W' : SeparatedOver site S hS B :=
    ⟨Over.mk (f' ≫ Z.hom),
      isSeparated_map_from_separated_scheme U hU (f ≫ Z.hom.hom)⟩
  refine ⟨W', Over.homMk f' rfl, ?_, ?_⟩
  · intro V φ hφ
    let P := MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme site S hS)
    have _ : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have _ : P.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    exact (P.relative yoneda).comp_mem φ f hφ he
  · exact (presheafSurjective_iff_isSurjective_yoneda site S hS
      Z.left.obj Z.left.property U f).mp hs

/-! ### Base changing the diagram along a morphism to the vertex -/

variable {B : AlgebraicSpaces site S hS} {I : Type v} [Category.{w} I]

/-- The base change of a diagram of separated algebraic spaces over `B` along a morphism to the
vertex of a cocone on it. -/
private noncomputable abbrev pullbackDiagram (D : I ⥤ SeparatedOver site S hS B)
    (s : Cocone (D ⋙ separatedOverInclusion site S hS B))
    {W : SeparatedOver site S hS B} (f : W.obj ⟶ s.pt) : I ⥤ SeparatedOver site S hS B where
  obj i := separatedPullback (s.ι.app i) f
  map {i j} k := separatedPullbackLift
    (separatedPullbackFst (s.ι.app i) f ≫ D.map k)
    (separatedPullbackSnd (s.ι.app i) f) (by
      apply Over.OverMorphism.ext
      have hk : (D.map k).hom.left ≫ (s.ι.app j).left = (s.ι.app i).left :=
        congrArg Over.Hom.left (s.w k)
      change (pullback.fst _ _ ≫ (D.map k).hom.left) ≫ (s.ι.app j).left =
        pullback.snd _ _ ≫ f.left
      rw [Category.assoc, hk, pullback.condition])
  map_id i := by
    apply separatedPullback_hom_ext
    all_goals simp [separatedPullbackLift_fst, separatedPullbackLift_snd]
  map_comp k l := by
    apply separatedPullback_hom_ext
    · simp only [Functor.map_comp]
      conv_rhs => rw [Category.assoc, separatedPullbackLift_fst,
        ← Category.assoc, separatedPullbackLift_fst]
      rw [separatedPullbackLift_fst, Category.assoc]
    · conv_rhs => rw [Category.assoc, separatedPullbackLift_snd,
        separatedPullbackLift_snd]
      exact separatedPullbackLift_snd _ _ _

/-- The projection of a base changed diagram onto the original diagram. -/
private noncomputable abbrev pullbackDiagramProjection (D : I ⥤ SeparatedOver site S hS B)
    (s : Cocone (D ⋙ separatedOverInclusion site S hS B))
    {W : SeparatedOver site S hS B} (f : W.obj ⟶ s.pt) : pullbackDiagram D s f ⟶ D where
  app i := separatedPullbackFst (s.ι.app i) f
  naturality i j k := by
    dsimp only [pullbackDiagram]
    rw [separatedPullbackLift_fst]

/-- The cocone on a base changed diagram with vertex the base changing object. -/
private noncomputable abbrev pullbackDiagramCocone (D : I ⥤ SeparatedOver site S hS B)
    (s : Cocone (D ⋙ separatedOverInclusion site S hS B))
    {W : SeparatedOver site S hS B} (f : W.obj ⟶ s.pt) : Cocone (pullbackDiagram D s f) where
  pt := W
  ι :=
    { app i := separatedPullbackSnd (s.ι.app i) f
      naturality i j k := by
        dsimp only [pullbackDiagram, Functor.const_obj_map]
        rw [separatedPullbackLift_snd]
        exact (Category.comp_id _).symm }

/-- The comparison squares of a base changed diagram are cartesian. -/
private theorem pullbackDiagram_isPullback (D : I ⥤ SeparatedOver site S hS B)
    (s : Cocone (D ⋙ separatedOverInclusion site S hS B))
    {W : SeparatedOver site S hS B} (f : W.obj ⟶ s.pt) (i : I) :
    IsPullback ((pullbackDiagramProjection D s f).app i).hom.left
      ((pullbackDiagramCocone D s f).ι.app i).hom.left (s.ι.app i).left f.left :=
  IsPullback.of_hasPullback (s.ι.app i).left f.left

/-- The transition squares of a base changed diagram are cartesian. -/
private theorem pullbackDiagram_cartesian (D : I ⥤ SeparatedOver site S hS B)
    (s : Cocone (D ⋙ separatedOverInclusion site S hS B))
    {W : SeparatedOver site S hS B} (f : W.obj ⟶ s.pt) {i j : I} (k : i ⟶ j) :
    IsPullback ((pullbackDiagram D s f).map k).hom.left
      ((pullbackDiagramProjection D s f).app i).hom.left
      ((pullbackDiagramProjection D s f).app j).hom.left (D.map k).hom.left := by
  have h₁ := congrArg (fun a => a.hom.left) ((pullbackDiagramCocone D s f).w k)
  have h₂ : (D.map k).hom.left ≫ (s.ι.app j).left = (s.ι.app i).left :=
    congrArg Over.Hom.left (s.w k)
  apply IsPullback.of_right _
    (congrArg (fun a => a.hom.left) ((pullbackDiagramProjection D s f).naturality k))
    (pullbackDiagram_isPullback D s f j).flip
  change ((pullbackDiagram D s f).map k).hom.left ≫
    ((pullbackDiagramCocone D s f).ι.app j).hom.left =
    ((pullbackDiagramCocone D s f).ι.app i).hom.left at h₁
  rw [h₁, h₂]
  exact (pullbackDiagram_isPullback D s f i).flip

/-! ### The colimit criterion -/

/-- **Stacks 0GFP.** Let `B` be an algebraic space over `S` and let `D` be a diagram of
algebraic spaces separated over `B`, with a colimit `c` in the category of algebraic spaces
separated over `B`. Assume that the members of the diagram jointly cover the vertex on points,
that every separated étale algebraic space over the vertex is the colimit of its base changes
to the members of the diagram, and that every compatible family of separated étale algebraic
spaces over the members of the diagram arises as the family of base changes of a separated
étale algebraic space over the vertex. Then `c` is a colimit of the diagram in the category of
*all* algebraic spaces over `B`. -/
@[stacks 0GFP "all five hypotheses; (1) carried by the diagram landing in the separated spaces \
over B, (2) by IsColimit of the cocone there, (3) stated as joint surjectivity on points, \
(4) and (5) stated with cartesian comparison squares"]
theorem isColimit_of_separated_etale_descent
    (D : I ⥤ SeparatedOver site S hS B) (c : Cocone D) (hc : IsColimit c)
    (hcover : ∀ x : points site S hS c.pt.obj.left.obj,
      ∃ i : I, ∃ y : points site S hS (D.obj i).obj.left.obj,
        pointsMap site S hS (D.obj i).obj.left.obj (c.ι.app i).hom.left.hom y = x)
    (hbase : ∀ (E : I ⥤ SeparatedOver site S hS B) (p : E ⟶ D) (d : Cocone E)
      (q : d.pt ⟶ c.pt), IsEtaleSeparated site S hS q →
      (∀ i : I, IsPullback (p.app i).hom.left (d.ι.app i).hom.left
        (c.ι.app i).hom.left q.hom.left) → IsColimit d)
    (hdesc : ∀ (E : I ⥤ SeparatedOver site S hS B) (p : E ⟶ D),
      (∀ i : I, IsEtaleSeparated site S hS (p.app i)) →
      (∀ {i j : I} (f : i ⟶ j), IsPullback (E.map f).hom.left (p.app i).hom.left
        (p.app j).hom.left (D.map f).hom.left) →
      ∃ (d : Cocone E) (q : d.pt ⟶ c.pt), IsEtaleSeparated site S hS q ∧
        ∀ i : I, IsPullback (p.app i).hom.left (d.ι.app i).hom.left
          (c.ι.app i).hom.left q.hom.left) :
    Nonempty (IsColimit ((separatedOverInclusion site S hS B).mapCocone c)) := by
  classical
  refine ⟨IsColimit.ofExistsUnique (fun s => ?_)⟩
  obtain ⟨W, f, hfe, hfs⟩ := exists_separated_etale_cover s.pt
  let E := pullbackDiagram D s f
  let p := pullbackDiagramProjection D s f
  let t := pullbackDiagramCocone D s f
  have hp (i : I) : IsEtaleSeparated site S hS (p.app i) :=
    ⟨isEtale_of_isPullback site S hS _ _ _ _ (pullbackDiagram_isPullback D s f i).flip hfe,
      separated_of_source (E.obj i) (p.app i).hom⟩
  have hps (i : I) : IsSurjective site S hS (p.app i).hom.left.hom :=
    isSurjective_of_isPullback site S hS (pullbackDiagram_isPullback D s f i).flip hfs
  obtain ⟨d, q, hq, hpb⟩ := hdesc E p hp (pullbackDiagram_cartesian D s f)
  have hd : IsColimit d := hbase E p d q hq hpb
  have hqs := surjective_of_commuting_jointly_surjective_family q.hom.left
    (fun i => (D.obj i).obj.left) (fun i => (E.obj i).obj.left)
    (fun i => (c.ι.app i).hom.left) (fun i => (d.ι.app i).hom.left)
    (fun i => (p.app i).hom.left) hcover hps (fun i => (hpb i).w.symm)
  let h := hd.desc t
  let g : d.pt.obj ⟶ s.pt := h.hom ≫ f
  have hg (i : I) : (d.ι.app i).hom ≫ g = (p.app i).hom ≫ s.ι.app i := by
    show (d.ι.app i).hom ≫ h.hom ≫ f = _
    rw [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, hd.fac]
    apply Over.OverMorphism.ext
    exact (pullbackDiagram_isPullback D s f i).w.symm
  let R := separatedPullback q.hom q.hom
  let r₁ : R ⟶ d.pt := separatedPullbackFst q.hom q.hom
  let r₂ : R ⟶ d.pt := separatedPullbackSnd q.hom q.hom
  have hr : r₁ ≫ q = r₂ ≫ q := separatedOver_hom_ext pullback.condition
  let q₂ : R ⟶ c.pt := r₁ ≫ q
  have hq₂ : IsEtaleSeparated site S hS q₂ := by
    refine ⟨?_, separated_of_source R q₂.hom⟩
    exact isEtale_comp site S hS
      (isEtale_of_isPullback site S hS _ _ _ _
        (IsPullback.of_hasPullback q.hom.left q.hom.left).flip hq.1) hq.1
  let c' := (separatedOverInclusion site S hS B).mapCocone c
  let E₂ := pullbackDiagram D c' q₂.hom
  let p₂ := pullbackDiagramProjection D c' q₂.hom
  let d₂ := pullbackDiagramCocone D c' q₂.hom
  have hd₂ : IsColimit d₂ := hbase E₂ p₂ d₂ q₂ hq₂
    (fun i => pullbackDiagram_isPullback D c' q₂.hom i)
  have hgg : r₁.hom ≫ g = r₂.hom ≫ g := by
    apply hom_ext_of_separated_colimit hd₂
    intro i
    apply Over.OverMorphism.ext
    have hwi : (p₂.app i).hom.left ≫ (c.ι.app i).hom.left =
        (d₂.ι.app i).hom.left ≫ q₂.hom.left :=
      (pullbackDiagram_isPullback D c' q₂.hom i).w
    show ((d₂.ι.app i).hom.left ≫ r₁.hom.left) ≫ g.left =
      ((d₂.ι.app i).hom.left ≫ r₂.hom.left) ≫ g.left
    apply pullback_hom_agree (hpb i) (congrArg Over.Hom.left (hg i)) (p₂.app i).hom.left
    · exact hwi.trans (Category.assoc _ _ _).symm
    · exact hwi.trans ((congrArg
        (fun k : R ⟶ c.pt => (d₂.ι.app i).hom.left ≫ k.hom.left) hr).trans
          (Category.assoc _ _ _).symm)
  have hcompat (T : AlgebraicSpaces site S hS) (a b : T ⟶ d.pt.obj.left)
      (hab : a ≫ q.hom.left = b ≫ q.hom.left) : a ≫ g.left = b ≫ g.left := by
    have hgg' : pullback.fst q.hom.left q.hom.left ≫ g.left =
        pullback.snd q.hom.left q.hom.left ≫ g.left := congrArg Over.Hom.left hgg
    have hh := congrArg (fun k => pullback.lift a b hab ≫ k) hgg'
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using hh
  obtain ⟨l, hl, -⟩ := existsUnique_desc_of_etale_surjective q.hom.left hq.1 hqs g.left hcompat
  have hlB : l ≫ s.pt.hom = c.pt.obj.hom := by
    apply etale_surjective_hom_ext q.hom.left hq.1 hqs
    rw [← Category.assoc, hl, Over.w, Over.w]
  let l' : c.pt.obj ⟶ s.pt := Over.homMk l hlB
  have hfac (i : I) : (c.ι.app i).hom ≫ l' = s.ι.app i := by
    apply Over.OverMorphism.ext
    apply etale_surjective_hom_ext (p.app i).hom.left (hp i).1 (hps i)
    show (p.app i).hom.left ≫ (c.ι.app i).hom.left ≫ l =
      (p.app i).hom.left ≫ (s.ι.app i).left
    rw [← Category.assoc, (hpb i).w, Category.assoc, hl]
    exact congrArg Over.Hom.left (hg i)
  exact ⟨l', hfac, fun m hm => hom_ext_of_separated_colimit hc fun i => (hm i).trans (hfac i).symm⟩

end AlgebraicGeometry.Space

end
