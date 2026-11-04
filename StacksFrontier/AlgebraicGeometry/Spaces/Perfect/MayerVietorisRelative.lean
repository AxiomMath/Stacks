module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
import StacksCore.Tactic.StacksAttribute

/-!
# Relative Mayer–Vietoris for an elementary distinguished square

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square on `X`, with intersection
`P = U ×_X V`.  Write `a = f|_U`, `b = f|_V` and `c = f|_P` for the restrictions of `f`.
Stacks 08JK says that every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

in `D(𝒪_Y)`, functorially in `E`.

## Main results

* `CategoryTheory.PushforwardMayerVietoris.shortExact_map_mayerVietoris_at_injective`: an
  additive functor carries the Mayer–Vietoris short exact sequence at an *injective* object to
  a short exact sequence.  This is the pivot of the whole file: the sequence at an injective
  object splits, and a split short exact sequence is preserved by any additive functor, so no
  exactness of the functor is needed.
* `CategoryTheory.PushforwardMayerVietoris.epi_conjugate_of_injective`: at an injective object
  the direct-image Mayer–Vietoris sequence is surjective on the right, granted of the
  extension-by-zero sequence of Stacks 08GV part (1) only that its first map is a
  monomorphism.  This is the step that Stacks 08GW part (1) leaves open at a general module.
* `CategoryTheory.PushforwardMayerVietoris.mem_distTriang_mapMayerVietoris_of_degreewise`
  `_shortExact`: the triangle of the image under an additive functor of the Mayer–Vietoris
  sequence of cochain complexes.
* `CategoryTheory.PushforwardMayerVietoris`
  `.exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives` and
  `…exists_mem_distTriang_mapMayerVietoris`: the abstract form of both tags.  Given the
  Mayer–Vietoris short exact sequence of endofunctors
  `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` — at the injective objects alone, which is all the proof
  uses — and an additive functor `G`, every object of `D(A)` sits in a distinguished triangle
  of the right derived functors of `G`, `Φ_U ⋙ G`, `Φ_V ⋙ G` and `Φ_P ⋙ G`.
* `CategoryTheory.PushforwardMayerVietoris.shortExact_mayerVietoris_self`: the Mayer–Vietoris
  hypothesis is *satisfiable* — for `Φ_V = 𝟭`, `Φ_P = Φ_U`, `d_U = 𝟙` and `d_V = η_U` the
  sequence is split short exact for every `η_U`, with no hypothesis at all.  This is the
  configuration of the elementary distinguished square `(U ⊆ X, 𝟙_X)`.
* `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`: the
  direct-image Mayer–Vietoris sequence of Stacks 08GW part (1) *at an injective module*, with
  nothing granted.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional`: the
  `@[stacks 08JK]` **registration** of the first of the tag's two assertions, the distinguished
  triangle.  It takes no hypothesis: only the square, `f`, and the four right derived functors
  with their comparisons.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris`: the same triangle,
  verbatim, with the direct-image Mayer–Vietoris short exact sequence of Stacks 08GW part (1) as
  a hypothesis, which is the form a caller holding that sequence for its own choice of maps
  applies.  It carries no tag; the registration is the unconditional statement above.
The second assertion of Stacks 08JK, that the triangle is *functorial in `E`*, is registered in
the sibling module `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelativeFunctorial`
on `AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_`
`unconditional`, which likewise takes no hypothesis.  Those two are the tag's only two
registrations; each of the two modules also keeps the form that takes the sequence as a
hypothesis, untagged, for a caller that holds it.
Stacks 0CRS, the absolute statement, is in the sibling module
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisSections`, which takes the same
abstract triangle at the functor of global sections.

## Implementation notes

*Why an additive functor suffices, and why that is the whole point.*  The source deduces
Stacks 08JK by applying `Rf_*` to the triangle of Stacks 08GW part (2).  That route needs
`Rf_*` to be a triangulated functor.  The route taken here is shorter and needs nothing of the
kind.  Represent `E` by a complex `I` that is K-injective **and has injective terms** — Stacks
079P supplies both, the functorial K-injective resolution of a Grothendieck abelian category
being termwise injective.  The Mayer–Vietoris sequence of part (1) at the injective object
`I^n` is a short exact sequence whose first object is injective, hence *splits*; a split short
exact sequence is carried to a split short exact sequence by any additive functor.  So
`f_*` — which is only left exact — may be applied degreewise, and the triangle is the one
attached by Stacks 0152 to the resulting short exact sequence of cochain complexes.  Neither
right exactness of `f_*` nor triangulatedness of `Rf_*` is used.

*The derived functors are arbitrary choices*, as in
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris` and in
Stacks 08GE: each of the four appears as an argument together with the natural transformation
exhibiting it as a right derived functor, so the result applies to whichever model of
`Rf_*`, `Ra_*((-)|_U)`, … a caller holds.  Inhabitants are exhibited by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_mapMayerVietorisFunctor_modules`.

*`Ra_*((-)|_U)` is the right derived functor of `a_* ∘ (-)|_U`, and that functor is
`Φ_U ⋙ f_*`.*  The identification is Stacks 03LU: `j_{U,*} ⋙ f_* ≅ (j_U ≫ f)_* = a_*`, which
is `AlgebraicGeometry.Space.modulePushforwardCompIso`.  The statement below is phrased with
`etaleModulePullback ⋙ modulePushforward (j_U ≫ f)`, i.e. with `a_*((-)|_U)` itself, and
`AlgebraicGeometry.Space.edsRestrictPushOpenPushforwardIso` is the comparison that carries the
proof over.

*Extension by zero appears only at the very end.*  The abstract part of the file, and the
conditional form of the tag, mention only the *direct-image* sequence
`0 ⟶ M ⟶ j_{U,*}M|_U ⊕ j_{V,*}M|_V ⟶ j_{P,*}M|_P ⟶ 0`, which is Stacks 08GW part (1), built
from the units of the adjunctions `(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU and from two
comparison maps into `j_{P,*}`.  `j_!` enters in the final section, and only in a proof: the
sequence at an injective module is *deduced* there from the extension-by-zero sequence of
Stacks 08GV part (1), so the unconditional statements do not mention `j_!` either.

### What is proved

Everything the tag asserts, with nothing granted, which is why the tag is registered only on the
unconditional statements.  The hypothesis `hMV` of
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris` — the direct-image
sequence, i.e. Stacks 08GW part (1) — is discharged in
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional`, and the
route avoids what is still open about 08GW part (1).

* Only the sequence at an **injective** module is ever used, because the representative of `E`
  may be taken termwise injective (Stacks 079P,
  `AlgebraicGeometry.Space.exists_quasiIso_isKInjective_injective_modules`).  That is the
  content of
  `CategoryTheory.PushforwardMayerVietoris`
  `.exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives`.
* At an injective module the sequence is short exact outright, by
  `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective`.  Exactness at
  the first two spots is `CategoryTheory.PushforwardMayerVietoris.exact_and_mono_conjugate`,
  which needs only part (1) of Stacks 08GV — that is
  `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`.  Surjectivity on the right, which
  `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris` carries as the hypothesis
  `hepi`, is at an injective module the extension of a counit along a monomorphism:
  `CategoryTheory.PushforwardMayerVietoris.epi_conjugate_of_injective`.  That weaker form is all
  this file needs; it is *not* the only one available, since
  `CategoryTheory.PushforwardMayerVietoris.epi_conjugate` now proves the surjectivity at **every**
  module in any abelian category with enough injectives, so Stacks 08GW is unqualified.
* *Functoriality in `E`*, the tag's second assertion, is proved in the sibling module
  `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelativeFunctorial`, also
  unconditionally
  (`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_`
  `unconditional`).  What is delivered *in this module* is the triangle at each object `E`
  separately, with the five morphisms existentially quantified; the two further steps
  functoriality needs — the comparison `Q(Ψ(Res K)) ≅ RΨ(Q K)` as a natural isomorphism of
  functors on `CochainComplex A ℤ`, built from the *functorial* K-injective resolution of
  Stacks 079P, and a descent of natural transformations through the localization
  `CategoryTheory.Localization.liftNatTrans` — are carried out there.

The forms that take the sequence as a hypothesis are kept beside the unconditional ones, but
carry no tag: they are what a caller holding the direct-image sequence for *its own* choice of
unit and comparison maps applies, which is how Stacks 0CRS consumes the abstract triangle.

## References

* [Stacks Project, Tag 08JK](https://stacks.math.columbia.edu/tag/08JK)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.PushforwardMayerVietoris

/-! ### An additive functor applied to the Mayer–Vietoris sequence -/

section MapMayerVietoris

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive]

/-- An additive functor carries the composite `X ⟶ Y₁ ⊞ Y₂ ⟶ Z` of the Mayer–Vietoris shape to
the composite of the images. -/
private lemma map_lift_desc_comp {D E : Type*} [Category D] [Category E] [Preadditive D]
    [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E] (F : D ⥤ E) [F.Additive]
    {X Y₁ Y₂ Z : D} (a : X ⟶ Y₁) (b : X ⟶ Y₂) (c : Y₁ ⟶ Z) (d : Y₂ ⟶ Z) :
    F.map (biprod.lift a b ≫ biprod.desc c (-d)) =
      biprod.lift (F.map a) (F.map b) ≫ biprod.desc (F.map c) (-F.map d) := by
  rw [← F.map_neg, ← F.biprodIsoOfAdditive_hom_map_lift Y₁ Y₂ a b,
    ← F.biprodIsoOfAdditive_inv_map_desc Y₁ Y₂ c (-d), assoc, Iso.hom_inv_id_assoc,
    F.map_comp]

/-- The image under an additive functor of a Mayer–Vietoris short complex is isomorphic, by the
biproduct comparison, to the Mayer–Vietoris short complex of the images. -/
private def mapLiftDescIso {D E : Type*} [Category D] [Category E] [Preadditive D]
    [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E] (F : D ⥤ E) [F.Additive]
    {X Y₁ Y₂ Z : D} {a : X ⟶ Y₁} {b : X ⟶ Y₂} {c : Y₁ ⟶ Z} {d : Y₂ ⟶ Z}
    (h : biprod.lift a b ≫ biprod.desc c (-d) = 0) :
    (ShortComplex.mk _ _ h).map F ≅ ShortComplex.mk (biprod.lift (F.map a) (F.map b))
      (biprod.desc (F.map c) (-F.map d)) (by rw [← map_lift_desc_comp, h, F.map_zero]) :=
  ShortComplex.isoMk (Iso.refl _) (F.biprodIsoOfAdditive Y₁ Y₂) (Iso.refl _)
    (by simpa using (F.biprodIsoOfAdditive_hom_map_lift Y₁ Y₂ a b).symm)
    (by simpa using ((Iso.inv_comp_eq _).1
      (F.biprodIsoOfAdditive_inv_map_desc Y₁ Y₂ c (-d))).symm)

omit [ΦU.Additive] [ΦV.Additive] [ΦP.Additive] [G.Additive] in
include hzero in
/-- The image under an additive functor of the Mayer–Vietoris complex is a complex. -/
lemma zero_map_mayerVietoris (M : A) :
    biprod.lift (G.map (ηU.app M)) (G.map (ηV.app M)) ≫
      biprod.desc (G.map (dU.app M)) (-(G.map (dV.app M))) = 0 := by
  have h := hzero M
  rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero] at h
  rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero,
    ← G.map_comp, ← G.map_comp, h]

omit [ΦU.Additive] [ΦV.Additive] [ΦP.Additive] in
include hzero in
/-- **An additive functor carries the Mayer–Vietoris sequence at an injective object to a short
exact sequence**, granted that sequence *at that object alone*.

The sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` has injective first object, so its
monomorphism admits a retraction and the sequence splits; a split short exact sequence is
carried by any additive functor to a split short exact sequence.  *No exactness of `G` is
assumed* — this is what lets the direct image, which is only left exact, be applied degreewise
in Stacks 08JK, and global sections, which is only left exact, in Stacks 0CRS.

Only the short exactness at `M` is used, which is what makes the whole chain need the
Mayer–Vietoris sequence at injective objects only; see
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional`. -/
lemma shortExact_map_mayerVietoris_at_injective (M : A) (hM : Injective M)
    (hMV : (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact) :
    (ShortComplex.mk (biprod.lift (G.map (ηU.app M)) (G.map (ηV.app M)))
      (biprod.desc (G.map (dU.app M)) (-(G.map (dV.app M))))
      (zero_map_mayerVietoris ηU ηV dU dV hzero G M)).ShortExact := by
  have := hM
  exact ShortComplex.shortExact_of_iso (mapLiftDescIso G (hzero M))
    (hMV.splittingOfInjective.map G).shortExact

omit [ΦU.Additive] [ΦV.Additive] [ΦP.Additive] in
include hzero in
/-- `CategoryTheory.PushforwardMayerVietoris.shortExact_map_mayerVietoris_at_injective` granted
the Mayer–Vietoris sequence at every object rather than at the injective object in question. -/
lemma shortExact_map_mayerVietoris_of_injective
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (M : A) (hM : Injective M) :
    (ShortComplex.mk (biprod.lift (G.map (ηU.app M)) (G.map (ηV.app M)))
      (biprod.desc (G.map (dU.app M)) (-(G.map (dV.app M))))
      (zero_map_mayerVietoris ηU ηV dU dV hzero G M)).ShortExact :=
  shortExact_map_mayerVietoris_at_injective ηU ηV dU dV hzero G M hM (hMV M)

/-- The map of cochain complexes `G K ⟶ G(Φ K)` obtained by applying `G` to a natural
transformation `𝟭 ⟶ Φ` degreewise. -/
def mapUnitCochainMap {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ) (K : CochainComplex A ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      ((Φ ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K where
  f n := G.map (η.app (K.X n))
  comm' i j _ := by
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map (η.naturality (K.d i j)).symm

/-- The degree `n` component of `mapUnitCochainMap G η K` is `G.map (η.app (K.X n))`. -/
@[simp]
lemma mapUnitCochainMap_f {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ)
    (K : CochainComplex A ℤ) (n : ℤ) :
    (mapUnitCochainMap G η K).f n = G.map (η.app (K.X n)) :=
  rfl

variable [HasDerivedCategory.{w'} C]

include hzero in
/-- **The triangle of the image of the Mayer–Vietoris sequence of a cochain complex.**  If the
image under `G` of the Mayer–Vietoris sequence is short exact at each term of a cochain complex
`K`, then the degreewise transformations fit into a distinguished triangle

`G K ⟶ G(Φ_U K) ⊕ G(Φ_V K) ⟶ G(Φ_P K) ⟶ (G K)[1]`

in `D(C)`.  No exactness of any of the four functors is used. -/
theorem mem_distTriang_mapMayerVietoris_of_degreewise_shortExact (K : CochainComplex A ℤ)
    (hex : ∀ n : ℤ, (ShortComplex.mk
      (biprod.lift (G.map (ηU.app (K.X n))) (G.map (ηV.app (K.X n))))
      (biprod.desc (G.map (dU.app (K.X n))) (-(G.map (dV.app (K.X n)))))
      (zero_map_mayerVietoris ηU ηV dU dV hzero G (K.X n))).ShortExact) :
    ∃ δ, Triangle.mk
        (biprod.lift (DerivedCategory.Q.map (mapUnitCochainMap G ηU K))
          (DerivedCategory.Q.map (mapUnitCochainMap G ηV K)))
        (biprod.desc
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Functor.whiskerRight dU G) (ComplexShape.up ℤ)).app K))
          (-(DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Functor.whiskerRight dV G) (ComplexShape.up ℤ)).app K))))
        δ ∈ distTriang (DerivedCategory C) := by
  let AU := ((ΦU ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let AV := ((ΦV ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let fU := mapUnitCochainMap G ηU K
  let fV := mapUnitCochainMap G ηV K
  let gU := (NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
    (ComplexShape.up ℤ)).app K
  let gV := (NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
    (ComplexShape.up ℤ)).app K
  have hz' : biprod.lift fU fV ≫ biprod.desc gU (-gV) = 0 := by
    ext n
    exact (map_lift_desc_comp (HomologicalComplex.eval C (ComplexShape.up ℤ) n) fU fV gU gV).trans
      (zero_map_mayerVietoris ηU ηV dU dV hzero G (K.X n))
  have hS : (ShortComplex.mk _ _ hz').ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
    exact ShortComplex.shortExact_of_iso (mapLiftDescIso _ hz').symm (hex n)
  have comm1 : biprod.lift (DerivedCategory.Q.map fU) (DerivedCategory.Q.map fV) ≫
      (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm.hom =
      (Iso.refl (DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom ≫
        DerivedCategory.Q.map (biprod.lift fU fV) :=
    (mapLiftDescIso DerivedCategory.Q hz').symm.hom.comm₁₂.symm
  have comm2 : biprod.desc (DerivedCategory.Q.map gU) (-(DerivedCategory.Q.map gV)) ≫
      (Iso.refl (DerivedCategory.Q.obj
        (((ΦP ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom =
      (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm.hom ≫
        DerivedCategory.Q.map (biprod.desc gU (-gV)) :=
    (mapLiftDescIso DerivedCategory.Q hz').symm.hom.comm₂₃.symm
  have comm3 : DerivedCategory.triangleOfSESδ hS ≫
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (Iso.refl (DerivedCategory.Q.obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom =
      (Iso.refl (DerivedCategory.Q.obj
        (((ΦP ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).hom ≫
        DerivedCategory.triangleOfSESδ hS := by
    simp
  exact ⟨DerivedCategory.triangleOfSESδ hS,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
      (Triangle.isoMk _ _ (Iso.refl _)
        (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm (Iso.refl _) comm1 comm2 comm3)⟩

end MapMayerVietoris

/-! ### Surjectivity of the direct-image sequence at an injective object -/

section ConjugateInjective

variable {A : Type u} [Category.{v} A] [Abelian A]
  {ΨU ΨV ΨP ΦU ΦV ΦP : A ⥤ A} [ΦP.Additive]
  (adjU : ΨU ⊣ ΦU) (adjV : ΨV ⊣ ΦV) (adjP : ΨP ⊣ ΦP)
  (α : ΨP ⟶ ΨU) (β : ΨP ⟶ ΨV)

/-- **At an injective object the direct-image Mayer–Vietoris sequence is surjective on the
right**, granted of the extension-by-zero sequence only that its first map is a monomorphism.

This is the one step of Stacks 08GW part (1) that
`CategoryTheory.PushforwardMayerVietoris.shortExact_conjugate` leaves as the hypothesis `hepi`,
and at an injective object it is free of the sheaf-level input the source uses.  The restriction
to injective objects is not needed in general —
`CategoryTheory.PushforwardMayerVietoris.epi_conjugate` discharges `hepi` at every object of an
abelian category with enough injectives — but it is what this file's consumers use, since the
representative of `E` may be taken termwise injective by Stacks 079P.  Write
`Ψ_Y ⊣ Φ_Y` for the three adjunctions — `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)` in the application
— and `d_Y` for the conjugate of `α`, resp. `β`.  Put `G = Φ_P F`.  Transposing across the
adjunctions turns a section of `d_U - d_V : Φ_U F ⊕ Φ_V F ⟶ Φ_P F` into an extension of the
counit `Ψ_P G ⟶ F` along `(α, -β) : Ψ_P G ⟶ Ψ_U G ⊕ Ψ_V G`, and that map is a monomorphism, so
`F` being injective supplies the extension.  The resulting section makes the map a split
epimorphism.

In the source this is the statement that the obstruction to lifting a section lives in
`Ext¹(𝒪_X, F)`, which vanishes for `F` injective; the proof here is that observation carried
out by hand on hom-groups, so that no internal hom on the site is needed. -/
lemma epi_conjugate_of_injective
    (hmono : ∀ M, Mono (biprod.lift (α.app M) (-(β.app M)))) (F : A) [Injective F] :
    Epi (biprod.desc ((conjugateEquiv adjU adjP α).app F)
      (-((conjugateEquiv adjV adjP β).app F))) := by
  have := hmono (ΦP.obj F)
  -- extend the counit along the monomorphism of the extension-by-zero sequence
  obtain ⟨h, hc⟩ : ∃ h : ΨU.obj (ΦP.obj F) ⊞ ΨV.obj (ΦP.obj F) ⟶ F,
      biprod.lift (α.app (ΦP.obj F)) (-(β.app (ΦP.obj F))) ≫ h = adjP.counit.app F :=
    ⟨Injective.factorThru _ _, Injective.comp_factorThru _ _⟩
  have hdesc : biprod.desc (biprod.inl ≫ h) (biprod.inr ≫ h) = h := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  have hu : α.app (ΦP.obj F) ≫ (biprod.inl ≫ h) - β.app (ΦP.obj F) ≫ (biprod.inr ≫ h) =
      adjP.counit.app F := by
    have h' : biprod.lift (α.app (ΦP.obj F)) (-(β.app (ΦP.obj F))) ≫
        biprod.desc (biprod.inl ≫ h) (biprod.inr ≫ h) = adjP.counit.app F := by
      rw [hdesc]; exact hc
    rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg] at h'
    exact h'
  -- its two transposes section the map
  have key : biprod.lift (adjU.homEquiv (ΦP.obj F) F (biprod.inl ≫ h))
        (adjV.homEquiv (ΦP.obj F) F (biprod.inr ≫ h)) ≫
      biprod.desc ((conjugateEquiv adjU adjP α).app F)
        (-((conjugateEquiv adjV adjP β).app F)) = 𝟙 (ΦP.obj F) := by
    rw [biprod.lift_desc, Preadditive.comp_neg,
      homEquiv_comp_conjugateEquiv adjU adjP α (ΦP.obj F) F (biprod.inl ≫ h),
      homEquiv_comp_conjugateEquiv adjV adjP β (ΦP.obj F) F (biprod.inr ≫ h),
      Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← sub_eq_add_neg,
      ← Preadditive.comp_sub, ← ΦP.map_sub, hu]
    exact adjP.right_triangle_components F
  have : IsSplitEpi (biprod.desc ((conjugateEquiv adjU adjP α).app F)
      (-((conjugateEquiv adjV adjP β).app F))) := IsSplitEpi.mk' ⟨_, key⟩
  infer_instance

end ConjugateInjective

/-! ### The abstract form of both tags -/

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] {C : Type u'} [Category.{v'} C] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} C]

/-- **Stacks 079P with injective terms.**  Every object of the unbounded derived category is
`DerivedCategory.Q` of a complex that is K-injective *and termwise injective*, as soon as such
resolutions exist.  The functorial K-injective resolution of a Grothendieck abelian category is
termwise injective, so this is no stronger a demand than
`CategoryTheory.PushforwardMayerVietoris.exists_isKInjective_representative_of_universe`. -/
lemma exists_isKInjective_injective_representative
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (E : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ (∀ n, Injective (I.X n)) ∧
      Nonempty (DerivedCategory.Q.obj I ≅ E) := by
  obtain ⟨I, i, hI, hi, hinj⟩ := hres (DerivedCategory.Q.objPreimage E)
  have := hi
  exact ⟨I, hI, hinj, ⟨(asIso (DerivedCategory.Q.map i)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- A natural isomorphism of additive functors, applied degreewise to a cochain complex. -/
def mapHomologicalComplexIsoApp {F F' : A ⥤ C} [F.Additive] [F'.Additive] (θ : F ≅ F')
    (K : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K where
  hom := (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K
  inv := (NatTrans.mapHomologicalComplex θ.inv (ComplexShape.up ℤ)).app K
  hom_inv_id := by ext n; simp
  inv_hom_id := by ext n; simp

variable {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]
  (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
  (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
    biprod.desc (dU.app M) (-(dV.app M)) = 0)
  (G : A ⥤ C) [G.Additive]
  {ΨX ΨU ΨV ΨP : A ⥤ C} [ΨX.Additive] [ΨU.Additive] [ΨV.Additive] [ΨP.Additive]
  (θX : G ≅ ΨX) (θU : ΦU ⋙ G ≅ ΨU) (θV : ΦV ⋙ G ≅ ΨV) (θP : ΦP ⋙ G ≅ ΨP)

include hzero θX θU θV θP in
/-- **The abstract form of Stacks 08JK and of the triangle of Stacks 0CRS, needing the
Mayer–Vietoris sequence at injective objects only.**

This is `CategoryTheory.PushforwardMayerVietoris.exists_mem_distTriang_mapMayerVietoris` with
the hypothesis `hMV` demanded only at the *injective* objects of `A`.  That is all the proof
ever uses: the representative of `E` is a termwise injective complex, and the sequence enters
only at its terms.  The weakening is what makes the geometric statement unconditional —
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris_of_injective` proves the
direct-image sequence at an injective module outright from Stacks 08GV part (1), whereas
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris` states it at a general module
with that surjectivity as the hypothesis `hepi`.  `hepi` is itself a theorem,
`CategoryTheory.PushforwardMayerVietoris.epi_conjugate`, so the general form is available too;
the injective form is used here because it is the one the K-injective resolution supplies. -/
theorem exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (hMV : ∀ M, Injective M → (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : ΨX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : ΨU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : ΨV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : ΨP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (E : DerivedCategory A) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory C) := by
  obtain ⟨I, hI, hinj, ⟨e⟩⟩ := exists_isKInjective_injective_representative hres E
  have hres' : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i := by
    intro K
    obtain ⟨J, i, h1, h2, -⟩ := hres K
    exact ⟨J, i, h1, h2⟩
  obtain ⟨δ, hδ⟩ := mem_distTriang_mapMayerVietoris_of_degreewise_shortExact
    ηU ηV dU dV hzero G I (fun n =>
      shortExact_map_mayerVietoris_at_injective ηU ηV dU dV hzero G (I.X n) (hinj n)
        (hMV (I.X n) (hinj n)))
  have hξ : ∀ {F Ψ : A ⥤ C} [F.Additive] [Ψ.Additive] (θ : F ≅ Ψ)
      (R : DerivedCategory A ⥤ DerivedCategory C)
      (α : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ R)
      (hR : R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))),
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
        R.obj E := fun θ R α hR =>
    DerivedCategory.Q.mapIso (mapHomologicalComplexIsoApp θ I) ≪≫
      rightDerivedObjIsoOfKInjective hres' _ inferInstance R α hR I hI ≪≫ R.mapIso e
  refine ⟨(hξ θX RX αX hRX).inv ≫
      DerivedCategory.Q.map (mapUnitCochainMap G ηU I) ≫ (hξ θU RU αU hRU).hom,
    (hξ θX RX αX hRX).inv ≫
      DerivedCategory.Q.map (mapUnitCochainMap G ηV I) ≫ (hξ θV RV αV hRV).hom,
    (hξ θU RU αU hRU).inv ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dU G)
          (ComplexShape.up ℤ)).app I) ≫ (hξ θP RP αP hRP).hom,
    (hξ θV RV αV hRV).inv ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (Functor.whiskerRight dV G)
          (ComplexShape.up ℤ)).app I) ≫ (hξ θP RP αP hRP).hom,
    (hξ θP RP αP hRP).inv ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map (hξ θX RX αX hRX).hom,
    isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ (hξ θX RX αX hRX).symm
      (biprod.mapIso (hξ θU RU αU hRU).symm (hξ θV RV αV hRV).symm)
      (hξ θP RP αP hRP).symm ?_ ?_ ?_)⟩
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  · simp

include hzero θX θU θV θP in
/-- **The abstract form of Stacks 08JK and of the triangle of Stacks 0CRS.**

Let `A` be an abelian category admitting termwise injective K-injective resolutions, let
`Φ_U, Φ_V, Φ_P : A ⥤ A` be additive endofunctors and let `η_U : 𝟭 ⟶ Φ_U`, `η_V : 𝟭 ⟶ Φ_V`,
`d_U : Φ_U ⟶ Φ_P`, `d_V : Φ_V ⟶ Φ_P` be natural transformations whose Mayer–Vietoris sequence

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

is short exact for every object `M`.  Let `G : A ⥤ C` be *any additive functor*, let `Ψ_X`,
`Ψ_U`, `Ψ_V`, `Ψ_P` be additive functors isomorphic to `G`, `Φ_U ⋙ G`, `Φ_V ⋙ G` and
`Φ_P ⋙ G` — the isomorphisms let a caller present the four functors in whichever factored
form it holds them — and let `R_X`, `R_U`, `R_V`, `R_P` be right derived functors of the four.
Then every object `E` of `D(A)` sits in a distinguished triangle

`R_X E ⟶ R_U E ⊕ R_V E ⟶ R_P E ⟶ (R_X E)[1]`

in `D(C)`.

Neither right exactness of `G` nor triangulatedness of its derived functor is used: the
sequence at a termwise injective complex is degreewise split, and a split short exact sequence
survives any additive functor.  Only the sequence at the injective objects is used, which is
`CategoryTheory.PushforwardMayerVietoris`
`.exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives`. -/
theorem exists_mem_distTriang_mapMayerVietoris
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (i : K ⟶ J),
      J.IsKInjective ∧ QuasiIso i ∧ ∀ n, Injective (J.X n))
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RX RU RV RP : DerivedCategory A ⥤ DerivedCategory C)
    (αX : ΨX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RX)
    (αU : ΨU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : ΨV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : ΨP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (E : DerivedCategory A) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory C) :=
  exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives ηU ηV dU dV hzero G
    θX θU θV θP hres (fun M _ => hMV M) RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

/-- **The long exact cohomology sequence of a Mayer–Vietoris triangle.**  A distinguished
triangle `X ⟶ Y₁ ⊕ Y₂ ⟶ Z ⟶ X[1]` in a derived category has an exact homology sequence, which
at each `n` is the six-term exact sequence

`H^n X ⟶ H^n (Y₁ ⊕ Y₂) ⟶ H^n Z ⟶ H^{n+1} X ⟶ H^{n+1} (Y₁ ⊕ Y₂) ⟶ H^{n+1} Z`

— exactness being the fact that the homology functor of a derived category is homological.
Since `H^n` is additive, the middle terms are `H^n Y₁ ⊕ H^n Y₂`.  This is the passage from the
triangle of Stacks 0CRS to its long exact Mayer–Vietoris sequence, isolated so that it is
elaborated away from the heavy categories of the geometric application. -/
theorem exists_homologySequence_exact_of_exists_mem_distTriang
    {X₁ Y₁ Y₂ Z₁ : DerivedCategory C}
    (h : ∃ (fU : X₁ ⟶ Y₁) (fV : X₁ ⟶ Y₂) (gU : Y₁ ⟶ Z₁) (gV : Y₂ ⟶ Z₁)
        (δ : Z₁ ⟶ X₁⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory C)) :
    ∃ (fU : X₁ ⟶ Y₁) (fV : X₁ ⟶ Y₂) (gU : Y₁ ⟶ Z₁) (gV : Y₂ ⟶ Z₁)
        (δ : Z₁ ⟶ X₁⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
          distTriang (DerivedCategory C) ∧
        ∀ n : ℤ, ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅
          (Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ) n (n + 1) rfl).Exact := by
  obtain ⟨fU, fV, gU, gV, δ, hT⟩ := h
  exact ⟨fU, fV, gU, gV, δ, hT, fun n =>
    Functor.homologySequenceComposableArrows₅_exact _ _ hT n (n + 1) rfl⟩

end Derived

/-! ### The Mayer–Vietoris hypothesis is satisfiable -/

section Satisfiable

variable {A : Type u} [Category.{v} A] [Abelian A] {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ)

omit [Φ.Additive] in
/-- The Mayer–Vietoris complex of the configuration `Φ_V = 𝟭`, `Φ_P = Φ_U`, `d_U = 𝟙`,
`d_V = η_U` is a complex, for every `η_U : 𝟭 ⟶ Φ_U`. -/
lemma zero_mayerVietoris_self (M : A) :
    biprod.lift (η.app M) (𝟙 M) ≫ biprod.desc (𝟙 (Φ.obj M)) (-(η.app M)) = 0 := by
  simp

/-- **The Mayer–Vietoris hypothesis is satisfiable, with no hypothesis whatsoever.**  For
`Φ_V = 𝟭`, `Φ_P = Φ_U`, `η_V = 𝟙`, `d_U = 𝟙` and `d_V = η_U` the Mayer–Vietoris sequence

`0 ⟶ M ⟶ Φ_U M ⊕ M ⟶ Φ_U M ⟶ 0`

is split short exact for every natural transformation `η_U : 𝟭 ⟶ Φ_U` and every object `M`,
the splitting being `(biprod.snd, biprod.inl)`.

This is exactly the configuration of the elementary distinguished square `(U ⊆ X, 𝟙_X)`, for
which `V = X`, `P = U ×_X X = U`, `Φ_V = j_{X,*}((-)|_X) = 𝟭`, `Φ_P = Φ_U`, the unit `η_V` is
the identity and the two comparison maps into `Φ_P` are `𝟙` and `η_U`.  So the hypothesis
`hMV` of `AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris` and of
`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris` is not
vacuous, and the complement `T = |X| ∖ |U|` is unconstrained: it may be any nonempty closed
subset. -/
def splittingMayerVietorisSelf (M : A) :
    (ShortComplex.mk (biprod.lift (η.app M) (𝟙 M))
      (biprod.desc (𝟙 (Φ.obj M)) (-(η.app M))) (zero_mayerVietoris_self η M)).Splitting where
  r := biprod.snd
  s := biprod.inl
  f_r := by simp
  s_g := by simp
  id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [Preadditive.add_comp, Preadditive.comp_add]

omit [Φ.Additive] in
/-- The sequence of `CategoryTheory.PushforwardMayerVietoris.splittingMayerVietorisSelf` is
short exact. -/
lemma shortExact_mayerVietoris_self (M : A) :
    (ShortComplex.mk (biprod.lift (η.app M) (𝟙 M))
      (biprod.desc (𝟙 (Φ.obj M)) (-(η.app M)))
      (zero_mayerVietoris_self η M)).ShortExact :=
  (splittingMayerVietorisSelf η M).shortExact

end Satisfiable

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **Stacks 079P for the modules on an algebraic space, with injective terms.**  Every cochain
complex of `𝒪_F`-modules admits a quasi-isomorphism into a complex that is K-injective *and
termwise injective*.

This is `AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules` keeping the one further
property of the functorial K-injective resolution that it discards: the resolution of Stacks
079P is a complex of injective objects.  That property is what makes the Mayer–Vietoris
sequence degreewise split at the resolution, and hence survive a merely left exact functor. -/
theorem exists_quasiIso_isKInjective_injective_modules (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (K : CochainComplex (Modules.{u, u} B S hS F hF) ℤ) :
    ∃ (I : CochainComplex (Modules.{u, u} B S hS F hF) ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g ∧ ∀ n, Injective (I.X n) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    isGrothendieckAbelian_modules B S hS F hF
  obtain ⟨R⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u}
    (Modules.{u, u} B S hS F hF)
  exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K, R.injective K⟩

/-- **The right derived functor of an additive functor out of the `𝒪_X`-modules exists**, with
no further hypothesis: `Mod(𝒪_X)` is Grothendieck abelian, so Stacks 079P supplies K-injective
resolutions and Stacks 070K turns those into a pointwise right derived functor.

Applied to `f_*`, to `a_*((-)|_U)` and to the two remaining composites of the square this
exhibits inhabitants for the data `R_•`, `α_•` and `hR_•` of the two `@[stacks 08JK]` carriers,
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional` and
`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_unconditional`:
take `R_•` to be `CategoryTheory.Functor.totalRightDerived` and `α_•` its canonical unit.  So
those statements are not vacuous. -/
theorem hasRightDerivedFunctor_mapMayerVietorisFunctor_modules
    {X Z : AlgebraicSpaces B S hS}
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Z.1 Z.2)]
    (Φ : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2) [Φ.Additive] :
    (Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {Z : AlgebraicSpaces B S hS} (f : W ⟶ Z)

/-- **`f_* ∘ j_{U,*} ∘ (-)|_U` is `a_* ∘ (-)|_U`**, for `a = f|_U` the restriction of `f` to the
open subspace of an elementary distinguished square.  This is Stacks 03LU: the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` identifies `j_{U,*} ⋙ f_*` with
`(j_U ≫ f)_*`, and `j_U ≫ f` is `a`. -/
def edsRestrictPushOpenPushforwardIso :
    edsRestrictPushOpen B S hS hsq ⋙ modulePushforward B S hS f ≅
      etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f) :=
  Functor.isoWhiskerLeft _ (modulePushforwardCompIso B S hS (edsOpenHom B S hS hsq) f)

/-- **`f_* ∘ j_{V,*} ∘ (-)|_V` is `b_* ∘ (-)|_V`**, for `b = f|_V` the restriction of `f` to the
étale member of an elementary distinguished square.  See
`AlgebraicGeometry.Space.edsRestrictPushOpenPushforwardIso`. -/
def edsRestrictPushEtalePushforwardIso :
    edsRestrictPushEtale B S hS hsq ⋙ modulePushforward B S hS f ≅
      etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f) :=
  Functor.isoWhiskerLeft _ (modulePushforwardCompIso B S hS (edsEtaleHom B S hS hsq) f)

/-- **`f_* ∘ j_{P,*} ∘ (-)|_P` is `c_* ∘ (-)|_P`**, for `c = f|_{U ×_X V}` the restriction of `f`
to the intersection of an elementary distinguished square.  See
`AlgebraicGeometry.Space.edsRestrictPushOpenPushforwardIso`. -/
def edsRestrictPushInterPushforwardIso :
    edsRestrictPushInter B S hS hsq ⋙ modulePushforward B S hS f ≅
      etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f) :=
  Functor.isoWhiskerLeft _ (modulePushforwardCompIso B S hS (edsInterHom B S hS hsq) f)

variable [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Z.1 Z.2)]

/-- **The relative Mayer–Vietoris triangle with part (1) of Stacks 08GW as a hypothesis.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square on `X`, let `P = U ×_X V` and let
`a = f|_U`, `b = f|_V`, `c = f|_P` be the restrictions of `f` to the three.  Let `Rf_*`,
`Ra_*((-)|_U)`, `Rb_*((-)|_V)` and `Rc_*((-)|_P)` be right derived functors of `f_*`,
`a_*((-)|_U)`, `b_*((-)|_V)` and `c_*((-)|_P)`, with their comparisons.  Suppose part (1) of
Stacks 08GW holds: writing `Φ_Y = j_{Y,*}((-)|_Y)`, the sequence

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

is short exact for every sheaf of `𝒪_X`-modules `M`.  Then every object `E` of `D(𝒪_X)` sits in
a distinguished triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

in `D(𝒪_Y)`.

The proof does not apply `Rf_*` to the triangle of Stacks 08GW part (2), and so does not need
`Rf_*` to be triangulated.  It represents `E` by a complex that is K-injective and *termwise
injective* (Stacks 079P,
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_injective_modules`); the Mayer–Vietoris
sequence at an injective module splits, so the merely left exact `f_*` may be applied to it
degreewise, and the triangle is the one Stacks 0152 attaches to the resulting short exact
sequence of cochain complexes.

As in Stacks 08GV part (2) and Stacks 08GW part (2), the five morphisms are existentially
quantified; the source likewise only asserts that a triangle with these three terms exists.

**This declaration is not the carrier of Stacks 08JK**, and `hMV` is not something the tag
leaves open.  The first assertion of the tag is registered on
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_unconditional`, whose
conclusion is the one below verbatim and which takes no hypothesis at all: the sequence is
needed only at the injective modules, and there it is proved.  The second assertion,
*functoriality in `E`*, is registered on
`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_`
`unconditional` in the sibling module.  What the form below is for is a caller that already
holds the direct-image sequence for *its own* choice of unit and comparison maps — the shape in
which `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris`
(Stacks 08GW part (2)) carries it — so that the three statements compose. -/
theorem exists_mem_distTriang_edsRelativeMayerVietoris
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_mem_distTriang_mapMayerVietoris ηU ηV dU dV hzero (modulePushforward B S hS f)
    (Iso.refl _) (edsRestrictPushOpenPushforwardIso B S hS hsq f)
    (edsRestrictPushEtalePushforwardIso B S hS hsq f)
    (edsRestrictPushInterPushforwardIso B S hS hsq f)
    (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2) hMV
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

end Square

/-! ### Stacks 08JK with nothing granted -/

section Unconditional

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

/-- **Stacks 08GW part (1) at an injective module, with nothing granted.**  For an elementary
distinguished square `(U ⊆ X, j_V : V ⟶ X)` with intersection `P = U ×_X V`, a left adjoint
`j_{Y!}` of restriction along each of the three étale morphisms, and an *injective* sheaf of
`𝒪_X`-modules `F`, the direct-image sequence

`0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P ⟶ 0`

is short exact — the first map being the pair of canonical units and the second the difference
of the conjugates, under `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the two extension-by-zero
comparisons of the square.

`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietoris` is the same sequence at an
arbitrary module, stated with two hypotheses: part (1) of Stacks 08GV, proved as
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, and the surjectivity on the right.
Both are theorems — the second is
`CategoryTheory.PushforwardMayerVietoris.epi_conjugate`, which obtains it at every module from
enough injectives alone, without the étale-local vanishing of an obstruction in `Ext¹(𝒪_X, F)`
that the source argues through.  At an injective `F` there is a shorter route still:
`CategoryTheory.PushforwardMayerVietoris.epi_conjugate_of_injective` extracts the splitting by
hand from the monomorphism of the extension-by-zero sequence, so nothing is left to grant.

Injective modules are all the chain of Stacks 08JK needs: the complex representing an object of
`D(𝒪_X)` can be taken termwise injective, by Stacks 079P. -/
theorem shortExact_edsRestrictPushMayerVietoris_of_injective
    (F : Modules.{u, u} B S hS W.1 W.2) (hF : Injective F) :
    (ShortComplex.mk
      (biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
        ((edsAdjEtale B S hS hsq).unit.app F))
      (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
            ((edsAdjInter B S hS hsq).comp adjP)
            (edsShriekOpenComparison B S hS hsq adjU adjP)).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
            ((edsAdjInter B S hS hsq).comp adjP)
            (edsShriekEtaleComparison B S hS hsq adjV adjP)).app F)))
      (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
        (edsShriekOpenComparison B S hS hsq adjU adjP)
        (edsShriekEtaleComparison B S hS hsq adjV adjP)
        (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) F)).ShortExact := by
  have := hF
  have hmono : ∀ M, Mono (biprod.lift
      ((edsShriekOpenComparison B S hS hsq adjU adjP).app M)
      (-((edsShriekEtaleComparison B S hS hsq adjV adjP).app M))) :=
    fun M => (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP M).mono_f
  exact shortExact_conjugate_of_eq ((edsAdjOpen B S hS hsq).comp adjU)
    ((edsAdjEtale B S hS hsq).comp adjV) ((edsAdjInter B S hS hsq).comp adjP)
    adjU.counit adjV.counit (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) _ _
    (conjugateUnit_comp_counit (edsAdjOpen B S hS hsq) adjU).symm
    (conjugateUnit_comp_counit (edsAdjEtale B S hS hsq) adjV).symm F _
    (epi_conjugate_of_injective ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjEtale B S hS hsq).comp adjV) ((edsAdjInter B S hS hsq).comp adjP)
      (edsShriekOpenComparison B S hS hsq adjU adjP)
      (edsShriekEtaleComparison B S hS hsq adjV adjP) hmono F)

variable {Z : AlgebraicSpaces B S hS} (f : W ⟶ Z)
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS W.1 W.2)]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Z.1 Z.2)]

include adjU adjV adjP in
/-- **Stacks 08JK, the distinguished triangle**, granted of extension by zero only that it
exists.  See `AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris_`
`unconditional`, which instantiates the three adjunctions at the extensions by zero the library
constructs and so grants nothing at all. -/
theorem exists_mem_distTriang_edsRelativeMayerVietoris_of_shriek
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_mem_distTriang_mapMayerVietoris_of_shortExact_at_injectives
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp adjU)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekOpenComparison B S hS hsq adjU adjP))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp adjV)
      ((edsAdjInter B S hS hsq).comp adjP) (edsShriekEtaleComparison B S hS hsq adjV adjP))
    (zero_edsRestrictPushMayerVietoris B S hS hsq adjU adjV adjP
      (edsShriekOpenComparison B S hS hsq adjU adjP)
      (edsShriekEtaleComparison B S hS hsq adjV adjP)
      (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP))
    (modulePushforward B S hS f)
    (Iso.refl _) (edsRestrictPushOpenPushforwardIso B S hS hsq f)
    (edsRestrictPushEtalePushforwardIso B S hS hsq f)
    (edsRestrictPushInterPushforwardIso B S hS hsq f)
    (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2)
    (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
      adjU adjV adjP M hM)
    RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

/-- **Stacks 08JK, the distinguished triangle.**  This declaration is the `@[stacks 08JK]`
registration of the first of the tag's two assertions, and it takes no hypothesis.

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square on `X`, let `P = U ×_X V` and let
`a = f|_U`, `b = f|_V`, `c = f|_P` be the restrictions of `f` to the three.  Let `Rf_*`,
`Ra_*((-)|_U)`, `Rb_*((-)|_V)` and `Rc_*((-)|_P)` be right derived functors of `f_*`,
`a_*((-)|_U)`, `b_*((-)|_V)` and `c_*((-)|_P)`, with their comparisons.  Then every object `E`
of `D(𝒪_X)` sits in a distinguished triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊕ Rb_*(E|_V) ⟶ Rc_*(E|_{U ×_X V}) ⟶ (Rf_*E)[1]`

in `D(𝒪_Y)`.

The conclusion is that of the untagged
`AlgebraicGeometry.Space.exists_mem_distTriang_edsRelativeMayerVietoris` verbatim, with that
statement's one hypothesis discharged by a route the source does not take.  The source
deduces the direct-image Mayer–Vietoris sequence of Stacks 08GW part (1) at every module, and
gets surjectivity on the right from the étale-local vanishing of an obstruction class.  Only the
sequence at an *injective* module is used here — the representative of `E` may be taken
termwise injective, by Stacks 079P — and there the obstruction vanishes for a formal reason:
`CategoryTheory.PushforwardMayerVietoris.epi_conjugate_of_injective` splits the sequence by
extending a counit along the monomorphism that part (1) of Stacks 08GV provides
(`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`).  So nothing beyond Stacks 08GV
part (1), which the library proves, and Stacks 079P is needed.

The three extensions by zero are the ones the library constructs,
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, with their adjunctions; nothing about them is
assumed, and they do not appear in the statement.  The five morphisms are existentially
quantified at each `E`; the tag's second assertion, that the triangle is in addition
*functorial in `E`*, is registered on
`AlgebraicGeometry.Space.exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_`
`unconditional` in the sibling module.  Those two declarations are the only two
`@[stacks 08JK]` registrations. -/
@[stacks 08JK "FIRST ASSERTION: for every E of D(O_X) a distinguished triangle
Rf_*E -> Ra_*(E|_U) ⊕ Rb_*(E|_V) -> Rc_*(E|_{U x_X V}) -> (Rf_*E)[1] in D(O_Y), with no
hypothesis beyond the square, f and the four derived functors. The SECOND ASSERTION,
functoriality in E, is exists_natTrans_mem_distTriang_edsRelativeMayerVietoris_unconditional in
the sibling module. Proof route and provenance are in this theorem's docstring"]
theorem exists_mem_distTriang_edsRelativeMayerVietoris_unconditional
    (RX RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αX : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RX)
    (αU : (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        modulePushforward B S hS (edsOpenHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙
        modulePushforward B S hS (edsInterHom B S hS hsq ≫ f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRX : RX.IsRightDerivedFunctor αX
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (fU : RX.obj E ⟶ RU.obj E) (fV : RX.obj E ⟶ RV.obj E) (gU : RU.obj E ⟶ RP.obj E)
      (gV : RV.obj E ⟶ RP.obj E) (δ : RP.obj E ⟶ (RX.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift fU fV) (biprod.desc gU (-gV)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  exists_mem_distTriang_edsRelativeMayerVietoris_of_shriek B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq))
    f RX RU RV RP αX αU αV αP hRX hRU hRV hRP E

end Unconditional

end AlgebraicGeometry.Space

end
