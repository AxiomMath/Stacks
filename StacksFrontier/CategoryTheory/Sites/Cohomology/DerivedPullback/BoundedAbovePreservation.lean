module

public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import
  StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.PullbackOfApproximations
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The derived pullback preserves boundedness above

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi and let `E` be an object of
`D(O')` whose cohomology vanishes in degrees `> n`. Then the same holds for `Lf^* E`.

The derived pullback is *not* computed by degreewise pullback in general — that is the whole
reason it is derived — so the statement is not the exactness argument of
`Stacks.Cohomology.CohomologicalDescent.isLE_derivedPullback_obj`, which carries exactness of
`f^*` as a hypothesis. Instead `E` is represented by a complex of flat modules which vanishes
strictly above `n`: such a complex is K-flat with flat terms and bounded above, so the
comparison `Lf^* ⟶ f^*` of Stacks 06YY is invertible on it, and its degreewise pullback still
vanishes strictly above `n` because pullback is additive.

Two further pieces of general machinery are recorded here, both consumed by the
pseudo-coherence statements above.

* The bounded-above flat representative itself, which is the first half of the argument of
  Stacks 08G1 and is extracted so that it can be used without a Tor-amplitude hypothesis.
* The transport of a *strictly perfect approximation in degrees `> m`* — a morphism which is an
  isomorphism on cohomology in every degree `> m` and an epimorphism in degree `m` — through
  any triangulated functor of derived categories which preserves boundedness above. The
  dictionary between the two sides is
  `DerivedCategory.triangle_obj₃_isLE_of_approximation` and
  its converse: being an approximation in degrees `> m` is exactly the vanishing of the third
  vertex of the cone triangle in degrees `≥ m`, and that is a condition a bound-preserving
  functor carries.

Finally, an isomorphism of the underived pullbacks induces an isomorphism of the derived ones:
both are left derived functors of their underived counterparts and a left derived functor is
unique up to a unique isomorphism. This is the form in which a commuting square of ringed topoi
becomes a commuting square of derived pullbacks.

## Main results

* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE`: an object
  of `D(O)` bounded above by `n` is represented by a complex of flat modules strictly bounded
  above by `n`.
* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isLE_derivedPullback_obj_of_isMorphismOfSites`:
  the derived pullback preserves `IsLE n`.
* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE`: a bound-preserving
  triangulated functor of derived categories carries an approximation in degrees `> m` to one.
* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackIsoOfPullbackIso`: an
  isomorphism of the underived pullbacks induces one of the derived pullbacks.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u v w d

/-! ### A bounded above flat representative -/

section FlatRepresentative

-- The sections universe `w` is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (Y : RingedSite.{u, v, max u v}) [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]

/-- **An object of `D(O)` bounded above by `n` has a flat representative strictly bounded above
by `n`.** This is the first half of the argument of Stacks 08G1, with no Tor-amplitude
hypothesis: the object is the image of a complex which is strictly bounded above by `n`
(`DerivedCategory.exists_iso_Q_obj_of_isLE`), and Stacks 05T7 resolves that complex by one with
flat terms which is still strictly bounded above by `n`, flat modules covering by Stacks
03EW. -/
theorem exists_flatRepresentative_of_isLE
    (E : RingedSite.DerivedModules.{u, v, max u v, d} Y) (n : ℤ) (hE : E.IsLE n) :
    ∃ K : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v}
        (O := Y.O) (K.X i)) ∧
      K.IsStrictlyLE n ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E n
  let Pflat : ObjectProperty (RingedSite.Modules.{u, v, max u v} Y) := fun F =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) F
  have _ : Pflat.ContainsZero :=
    ⟨⟨kernel (𝟙 (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))), isZero_kernel_of_mono _,
        Stacks.SheafOfModules.DerivedTensorProduct.isFlat_kernel_id_unit (Y := Y)⟩⟩
  have hcover : ∀ F : RingedSite.Modules.{u, v, max u v} Y,
      ∃ (G : RingedSite.Modules.{u, v, max u v} Y) (_ : Pflat G) (g : G ⟶ F), Epi g := fun F => by
    obtain ⟨G, g, hG, hg⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat Y.O F
    exact ⟨G, hG, g, hg⟩
  obtain ⟨P, g, -, hg, hPflat, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat hcover n).1 M
  have _ : QuasiIso g := hg
  exact ⟨P, hPflat, hPLE, ⟨asIso (DerivedCategory.Q.map g) ≪≫ eM.symm⟩⟩

end FlatRepresentative

/-! ### The derived pullback preserves boundedness above -/

section Pullback

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

variable (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **A complex on which the canonical comparison of Stacks 06YY is invertible computes the
derived pullback.** For such a complex `K`, `Lf^* Q(K) ≅ Q(f^* K)`.

The comparison lives on the homotopy category, while both sides of the conclusion are stated
through `DerivedCategory.Q`; `DerivedCategory.quotientCompQhIso` is the bridge, and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` identifies degreewise pullback on the
homotopy category with degreewise pullback of complexes. -/
def derivedPullbackObjIsoOfIsIsoComparison
    (K : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app K).symm ≪≫
    asIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≪≫
    DerivedCategory.Qh.mapIso
      ((f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
      ((pullbackComplex f).obj K)

include hmos in
/-- **The derived pullback is computed by degreewise pullback on a bounded above flat
representative.** For a complex `K` of flat `O'`-modules which is strictly bounded above,
`Lf^* Q(K) ≅ Q(f^* K)`: such a `K` is K-flat with flat terms, so the canonical comparison of
Stacks 06YY is invertible on it. -/
def derivedPullbackObjIsoOfFlat
    (K : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (n : ℤ)
    (hKLE : K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  derivedPullbackObjIsoOfIsIsoComparison f K
    (isIso_derivedPullbackComparison_app_boundedAbove f hmos K ⟨n, hKLE⟩ hflat)

include hmos in
/-- **The derived pullback along a morphism of ringed topoi preserves boundedness above.** If
the cohomology of `E` vanishes in degrees `> n`, so does that of `Lf^* E`.

`E` is represented by a complex `K` of flat modules strictly bounded above by `n`
(`exists_flatRepresentative_of_isLE`); on such a `K` the derived pullback is the degreewise
pullback (`derivedPullbackObjIsoOfFlat`), and `f^* K` is again strictly bounded above by `n`
because an additive functor carries a zero object to a zero object. -/
theorem isLE_derivedPullback_obj_of_isMorphismOfSites
    (E : DerivedCategory (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (n : ℤ) (hE : E.IsLE n) :
    ((derivedPullback f).obj E).IsLE n := by
  obtain ⟨K, hflat, hKLE, ⟨e⟩⟩ :=
    exists_flatRepresentative_of_isLE Y.toRingedSite E n hE
  have hpLE : ((pullbackComplex f).obj K).IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => Functor.map_isZero f.pullbackTopos (K.isZero_of_isStrictlyLE n i hi)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedPullbackObjIsoOfFlat f hmos K n hKLE hflat).symm ≪≫
      (derivedPullback f).mapIso e) n

end Pullback

/-! ### Transporting an approximation along a bound-preserving functor -/

section Approximation

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]

/-- **A bound-preserving triangulated functor carries an approximation in degrees `> m` to
one.** Let `F : D(A) ⥤ D(B)` be triangulated and suppose `F` keeps every object of `D^{≤n}` in
`D^{≤n}`. If `α : P ⟶ E` is an isomorphism on cohomology in every degree `> m` and an
epimorphism in degree `m`, then `F α` has the same two properties.

Being an approximation in degrees `> m` is, by
`DerivedCategory.triangle_obj₃_isLE_of_approximation` and its
converse, exactly the statement that the third vertex of a distinguished triangle on `α` is
bounded above by `m - 1`; a triangulated `F` carries that triangle to a distinguished triangle
and, by hypothesis, keeps the bound. -/
theorem map_approximation_of_isLE (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
    [F.IsTriangulated] (hF : ∀ (K : DerivedCategory A) (n : ℤ), K.IsLE n → (F.obj K).IsLE n)
    {P E : DerivedCategory A} (α : P ⟶ E) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor A i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor A m).map α)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor B i).map (F.map α))) ∧
      Epi ((DerivedCategory.homologyFunctor B m).map (F.map α)) := by
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  exact DerivedCategory.approximation_of_triangle_isLE
    (F.mapTriangle.obj (Triangle.mk α β γ)) (F.map_distinguished _ hT) m
    (hF C (m - 1) (DerivedCategory.triangle_obj₃_isLE_of_approximation
      (Triangle.mk α β γ) hT m hiso hepi))

/-- **An approximation in degrees `> m` stays one after composing with an isomorphism.** -/
theorem approximation_comp_iso {P E E' : DerivedCategory A} (α : P ⟶ E) (e : E ≅ E') (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor A i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor A m).map α)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor A i).map (α ≫ e.hom))) ∧
      Epi ((DerivedCategory.homologyFunctor A m).map (α ≫ e.hom)) := by
  refine ⟨fun i hi => ?_, ?_⟩ <;> rw [Functor.map_comp]
  · have := hiso i hi
    infer_instance
  · infer_instance

/-- **An approximation in degrees `> m` stays one after composing with an isomorphism on the
left.** -/
theorem iso_comp_approximation {P' P E : DerivedCategory A} (e : P' ≅ P) (α : P ⟶ E) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor A i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor A m).map α)) :
    (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor A i).map (e.hom ≫ α))) ∧
      Epi ((DerivedCategory.homologyFunctor A m).map (e.hom ≫ α)) := by
  refine ⟨fun i hi => ?_, ?_⟩ <;> rw [Functor.map_comp]
  · have := hiso i hi
    infer_instance
  · infer_instance

/-- **A chain-level approximation in degrees `> m` becomes one in the derived category.** The
cohomology functors of the derived category restrict along `Q` to the cohomology functors of
complexes, by `DerivedCategory.homologyFunctorFactors`. -/
theorem approximation_Q_map {P K : CochainComplex A ℤ} (α : P ⟶ K) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ i : ℤ, m < i →
        IsIso ((DerivedCategory.homologyFunctor A i).map (DerivedCategory.Q.map α))) ∧
      Epi ((DerivedCategory.homologyFunctor A m).map (DerivedCategory.Q.map α)) :=
  ⟨fun i hi => (RingedSpace.KFlatDerivedPullback.isIso_homologyFunctor_map_Q_map_iff α i).2
      (hiso i hi),
    (RingedSpace.KFlatDerivedPullback.epi_homologyFunctor_map_Q_map_iff α m).2 hepi⟩

end Approximation

/-! ### Derived pullback along 2-isomorphic morphisms -/

section TwoIso

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

/-- **An isomorphism of the underived pullbacks induces an isomorphism of the derived
pullbacks.** Both derived pullbacks are total left derived functors of their underived
counterparts composed with localization, so this is uniqueness of a left derived functor,
`CategoryTheory.Functor.leftDerivedNatIso`.

This is the form in which a commuting square of ringed topoi — which Stacks expresses as a
2-isomorphism of the two composites, and which
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso` turns into an isomorphism of the
underived pullbacks — becomes a commuting square of derived pullbacks. -/
def derivedPullbackIsoOfPullbackIso (f g : RingedToposSiteHom X Y)
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    (e : f.pullbackTopos ≅ g.pullbackTopos) :
    derivedPullback f ≅ derivedPullback g :=
  Functor.leftDerivedNatIso (derivedPullback f) (derivedPullback g)
    (derivedPullbackComparison f) (derivedPullbackComparison g)
    (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)) DerivedCategory.Qh)

end TwoIso

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
