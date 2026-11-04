module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleStalkFiniteProducts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Étale sheaves supported in a specialization-closed set

Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under specialization. A torsion abelian
sheaf on the small étale site of `X` whose support lies in `E` is a filtered colimit of
constructible abelian sheaves, each of whose supports lies in a *closed* subset of `E`; and the
same holds for a sheaf of `Λ`-modules supported in `E`, with `Λ` a Noetherian ring. This is
Stacks 0F0N, parts (1) and (2).

The proof is the source's, and is short. Write the given sheaf as a filtered colimit `F = colim
F i` of constructible sheaves, which is Stacks 03SA, and replace each `F i` by the image `F' i`
of the leg `F i ⟶ F`. Three things then have to be checked, and the file does them in this
order.

* The images again form a filtered colimit with vertex `F`. This is general: each leg factors
  through its image by an epimorphism, so a cocone on the diagram of images lifts to one on the
  original diagram and the universal property transfers. That is
  `AlgebraicGeometry.imageDiagramCocone_isColimit`, proved for an arbitrary abelian category.
* Each `F' i` is constructible, being a quotient of `F i` — Stacks 09BH.
* The support of `F' i` lies in a closed subset of `E`. Since `F' i` is a subsheaf of `F`, its
  support lies in that of `F`, hence in `E`; the geometric stalk is a filtered colimit in a
  category satisfying AB5, so it is left exact and carries the inclusion to an injection. The
  support of a constructible sheaf is a constructible subset by Stacks 09YS, and a constructible
  subset of a specialization-closed set has its closure inside that set as well, by Stacks 0903.
  The closure is the required closed subset.

## What the two parts rest on

Part (2) is proved from the library alone. Stacks 03SA (3) enters as the unconditional
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`, which absorbs
both inputs that the conditional form of that tag used to pass on — Stacks 093C in the shriek
spelling and the sheaves-of-modules case of Stacks 03S8. Stacks 09BH (3) enters as the
unconditional `AlgebraicGeometry.isConstructibleModuleSheaf_forall_epi`, whose own geometric step
is `AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible`.

Part (1) is proved from the library as well. Its one input beyond the above, **Stacks 03SA (2)**
for torsion abelian sheaves, enters as the unconditional
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`, at the same
local notion of torsion as part (1) itself; the reduction
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support` takes it
in the spelling `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfConstructibles`, and
`exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support_of_torsion` supplies it.

Stacks 09BH (2) itself is now unconditional, so nothing of it is passed through:
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_epi` asks for none of its three former inputs.
Stacks 00YT is `AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`, Stacks 03S8 for a
representable sheaf of sets is `AlgebraicGeometry.representableIsConstructibleSetSheaf` and the
surjection half of Stacks 09Y9 is `AlgebraicGeometry.hasFiniteRepresentableCover`.

Stacks 00YT, Stacks 09YS (2) and (3), Stacks 0903, Stacks 095E, Stacks 09YR, Stacks 03RZ (3),
Stacks 03S8 for sheaves of sets and Stacks 03SA (3) are all discharged from the library.

## Main definitions

* `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfConstructibles` — Stacks 03SA (2),
  in the spelling the reduction of part (1) consumes.
* `AlgebraicGeometry.supportModuleSheaf` — the support of a sheaf of `Λ`-modules on the small
  étale site, the set whose constructibility is the library's Stacks 09YS (3).

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support` —
  Stacks 0F0N (1) given Stacks 03SA (2), which
  `exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support_of_torsion` supplies.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support` —
  Stacks 0F0N (2).

## Implementation notes

Torsion of an abelian sheaf is `Stacks.Torsion.torsionSheafProperty`, the site-level condition of
Stacks 0DD7 that every section be locally annihilated by a positive integer. It enters only
through Stacks 03SA (2); nothing below inspects it. Stacks 03SA (2) is used in the form
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`, stated at the
same `Stacks.Torsion.torsionSheafProperty`, and not in the form
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimitOfConstructibles`,
which is stated at `AlgebraicGeometry.IsTorsionAbelianSheaf`, annihilation object-by-object: that
is the stronger condition, so consuming it would strengthen the hypothesis of part (1).

The support of an abelian sheaf is `AlgebraicGeometry.supportSheaf`, the library's Stacks 04FS.
There is no corresponding definition for sheaves of modules, so
`AlgebraicGeometry.supportModuleSheaf` is introduced here, spelled exactly as the set appearing
in the conclusion of `AlgebraicGeometry.isConstructible_support_moduleSheaf`.

The coefficient universes are `AddCommGrpCat.{u + 1}` and `ModuleCat.{u + 1} Λ` for
`Λ : Type (u + 1)`, the universes at which Stacks 03SA and Stacks 09BH are stated in this
library. At those universes the instance families of Stacks 09YS have to be fixed by hand rather
than synthesized: the generic instance for presheaves of modules on a slice of the site is stated
at `ModuleCat.{max u v w}`, and instance search stalls on the resulting `max` constraint, so
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_over_moduleCat` records the
specialisation, and Stacks 09YS (3) is applied with its universes given explicitly.

The conclusions quantify over a diagram, a cocone whose point is literally the given sheaf, and
`Nonempty (IsColimit _)`, matching the shape of the library's Stacks 03SA so that the two
compose. `IsColimit` is data, so `Nonempty` is what makes the statement a proposition; no other
part of either conclusion is behind a `Nonempty`.

## References

* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 0903](https://stacks.math.columbia.edu/tag/0903)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 04FS](https://stacks.math.columbia.edu/tag/04FS)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The diagram of images of a cocone -/

variable {I : Type*} [Category I] {C : Type*} [Category C]

/-- The diagram of arrows `D i ⟶ F` attached to a cocone on `D` with vertex `F`. -/
private abbrev arrowDiagram (D : I ⥤ C) {F : C} (η : D ⟶ (Functor.const I).obj F) :
    I ⥤ Arrow C := {
  obj i := Arrow.mk (η.app i)
  map f := Arrow.homMk (D.map f) (𝟙 F) (by simp)
  map_id i := by ext <;> simp
  map_comp f g := by ext <;> simp
}

/-- The diagram of images of the legs of a cocone on `D` with vertex `F`. -/
private abbrev imageDiagram [Abelian C] (D : I ⥤ C) {F : C}
    (η : D ⟶ (Functor.const I).obj F) : I ⥤ C :=
  arrowDiagram D η ⋙ Abelian.im

/-- Taking images is compatible with the inclusions of the images into the common target. -/
private theorem abelianIm_map_image_ι [Abelian C] {f g : Arrow C} (u : f ⟶ g) :
    Abelian.im.map u ≫ Abelian.image.ι g.hom = Abelian.image.ι f.hom ≫ u.right := by
  dsimp [Abelian.im]
  rw [kernel.lift_ι]

/-- The inclusions of the images of the legs of a cocone into its vertex are compatible with
the maps of the image diagram. -/
private theorem imageDiagram_map_ι [Abelian C] (D : I ⥤ C) {F : C}
    (η : D ⟶ (Functor.const I).obj F) {i j : I} (f : i ⟶ j) :
    Abelian.im.map ((arrowDiagram D η).map f) ≫ Abelian.image.ι (η.app j) =
      Abelian.image.ι (η.app i) := by
  simpa [arrowDiagram] using abelianIm_map_image_ι ((arrowDiagram D η).map f)

/-- The cocone on the image diagram whose legs are the inclusions of the images into the
vertex of the given cocone. -/
private abbrev imageDiagramCocone [Abelian C] (D : I ⥤ C) {F : C}
    (η : D ⟶ (Functor.const I).obj F) : Cocone (imageDiagram D η) := {
  pt := F
  ι := {
    app i := Abelian.image.ι (η.app i)
    naturality := by
      intro i j f
      change Abelian.im.map ((arrowDiagram D η).map f) ≫ Abelian.image.ι (η.app j) =
        Abelian.image.ι (η.app i) ≫ ((Functor.const I).obj F).map f
      rw [imageDiagram_map_ι (D := D) (η := η) (f := f)]
      rw [Functor.const_obj_map]
      exact (Category.comp_id (Abelian.image.ι (η.app i))).symm
  }
}

/-- A cocone on the image diagram induces one on the original diagram, by composing with the
canonical epimorphisms onto the images. -/
private abbrev imageLiftCocone [Abelian C] (D : I ⥤ C) {F : C}
    (η : D ⟶ (Functor.const I).obj F) (s : Cocone (imageDiagram D η)) : Cocone D := {
  pt := s.pt
  ι := {
    app i := Abelian.factorThruImage (η.app i) ≫ s.ι.app i
    naturality := by
      intro i j f
      have hf : D.map f ≫ Abelian.factorThruImage (η.app j) =
          Abelian.factorThruImage (η.app i) ≫ (imageDiagram D η).map f := by
        apply (cancel_mono (Abelian.image.ι (η.app j))).1
        change (D.map f ≫ Abelian.factorThruImage (η.app j)) ≫ Abelian.image.ι (η.app j) =
          (Abelian.factorThruImage (η.app i) ≫
            Abelian.im.map ((arrowDiagram D η).map f)) ≫ Abelian.image.ι (η.app j)
        calc
          (D.map f ≫ Abelian.factorThruImage (η.app j)) ≫ Abelian.image.ι (η.app j) =
              D.map f ≫ (Abelian.factorThruImage (η.app j) ≫
                Abelian.image.ι (η.app j)) := by cat_disch
          _ = D.map f ≫ η.app j := by rw [Abelian.image.fac]
          _ = η.app i := by simp
          _ = Abelian.factorThruImage (η.app i) ≫ Abelian.image.ι (η.app i) :=
              (Abelian.image.fac (η.app i)).symm
          _ = Abelian.factorThruImage (η.app i) ≫
                (Abelian.im.map ((arrowDiagram D η).map f) ≫
                  Abelian.image.ι (η.app j)) :=
              congrArg (fun g => Abelian.factorThruImage (η.app i) ≫ g)
                (imageDiagram_map_ι D η f).symm
          _ = (Abelian.factorThruImage (η.app i) ≫
                (imageDiagram D η).map f) ≫ Abelian.image.ι (η.app j) :=
              (Category.assoc _ _ _).symm
      calc
        D.map f ≫ (Abelian.factorThruImage (η.app j) ≫ s.ι.app j) =
            (D.map f ≫ Abelian.factorThruImage (η.app j)) ≫ s.ι.app j :=
            (Category.assoc _ _ _).symm
        _ = (Abelian.factorThruImage (η.app i) ≫
              (imageDiagram D η).map f) ≫ s.ι.app j := by rw [hf]; rfl
        _ = Abelian.factorThruImage (η.app i) ≫
              ((imageDiagram D η).map f ≫ s.ι.app j) := Category.assoc _ _ _
        _ = Abelian.factorThruImage (η.app i) ≫ s.ι.app i :=
            congrArg (fun g => Abelian.factorThruImage (η.app i) ≫ g) (s.w f)
        _ = (Abelian.factorThruImage (η.app i) ≫ s.ι.app i) ≫
              ((Functor.const I).obj s.pt).map f := by
            rw [Functor.const_obj_map]
            exact (Category.comp_id _).symm
  }
}

/-- **The images of the legs of a colimit cocone form a colimit cocone on the same vertex.**
Each leg factors through its image by an epimorphism, so a cocone on the image diagram lifts to
one on the original diagram and the universal property transfers. -/
private def imageDiagramCocone_isColimit [Abelian C] (D : I ⥤ C) {F : C}
    (η : D ⟶ (Functor.const I).obj F) (hη : IsColimit (Cocone.mk F η)) :
    IsColimit (imageDiagramCocone D η) := by
  refine IsColimit.mk (fun s => hη.desc (imageLiftCocone D η s)) ?_ ?_
  · intro s i
    apply (cancel_epi (Abelian.factorThruImage (η.app i))).1
    calc
      Abelian.factorThruImage (η.app i) ≫
          (Abelian.image.ι (η.app i) ≫ hη.desc (imageLiftCocone D η s)) =
        (Abelian.factorThruImage (η.app i) ≫ Abelian.image.ι (η.app i)) ≫
          hη.desc (imageLiftCocone D η s) := (Category.assoc _ _ _).symm
      _ = η.app i ≫ hη.desc (imageLiftCocone D η s) := by rw [Abelian.image.fac]
      _ = (imageLiftCocone D η s).ι.app i := hη.fac _ _
      _ = Abelian.factorThruImage (η.app i) ≫ s.ι.app i := by
        simp [imageLiftCocone]
  · intro s m hm
    apply hη.uniq (imageLiftCocone D η s)
    intro i
    calc
      η.app i ≫ m = Abelian.factorThruImage (η.app i) ≫
          (Abelian.image.ι (η.app i) ≫ m) := by
            rw [← Category.assoc, Abelian.image.fac]
      _ = Abelian.factorThruImage (η.app i) ≫ s.ι.app i :=
        congrArg (fun g => Abelian.factorThruImage (η.app i) ≫ g) (hm i)

/-! ### The support of a subsheaf -/

/-- A geometric stalk is a filtered colimit taken in a category satisfying AB5, hence left exact,
so it carries a monomorphism of sheaves to a monomorphism; a subsheaf of a sheaf with zero stalk
at `p` therefore has zero stalk at `p`. -/
private theorem isZero_etaleStalk_of_mono (B : BigEtaleSite.{u}) (X : B.Scheme)
    (p : GeometricPoint X.obj) (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [HasFilteredColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
    [HasColimitsOfShape (geometricPointFiber B X.obj X.property p).Elementsᵒᵖ A]
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) A) (i : F ⟶ G) [Mono i]
    (hzero : IsZero (etaleStalk B X.obj X.property p G.obj)) :
    IsZero (etaleStalk B X.obj X.property p F.obj) := by
  let FtoP := sheafToPresheaf (SmallEtale.topology B X.obj X.property) A
  let St := etaleStalkPresheafFunctor B X.obj X.property p A
  let : HasExactColimitsOfShape
      (geometricPointFiber B X.obj X.property p).Elementsᵒᵖ A :=
    hasExactColimitsOfShape_of_final A
      (FinallySmall.fromFilteredFinalModel.{u}
        ((geometricPointFiber B X.obj X.property p).Elementsᵒᵖ))
  let : PreservesFiniteLimits St := by
    dsimp [St, etaleStalkPresheafFunctor]
    infer_instance
  let : Mono (FtoP.map i) := (sheafToPresheaf _ _).map_mono i
  have hmono : Mono (St.map (FtoP.map i)) := preserves_mono_of_preservesLimit St (FtoP.map i)
  have hId : 𝟙 (St.obj (FtoP.obj F)) = 0 :=
    hmono.right_cancellation (𝟙 _) 0 <| by
      calc 𝟙 _ ≫ St.map (FtoP.map i) = St.map (FtoP.map i) := by simp
        _ = 0 := hzero.eq_of_tgt (St.map (FtoP.map i)) 0
        _ = 0 ≫ St.map (FtoP.map i) := by simp
  exact (IsZero.iff_id_eq_zero _).2 hId

/-- **The support of a subsheaf is contained in the support of the ambient sheaf.** -/
private theorem supportSheaf_subset_of_mono (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (i : F ⟶ G) [Mono i] :
    supportSheaf B X.obj X.property F ⊆ supportSheaf B X.obj X.property G := by
  intro x hx
  rw [mem_supportSheaf_iff_exists] at hx ⊢
  simp only [isZero_etaleStalk_ulift_iff] at hx ⊢
  obtain ⟨p, hp, hn⟩ := hx
  let : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1, u + 1, u + 2} AddCommGrpCat.{u + 1}
  exact ⟨p, hp, fun hzero => hn (isZero_etaleStalk_of_mono B X p _ F G i hzero)⟩

/-! ### Closures of constructible subsets of specialization-closed sets -/

/-- **Stacks 0903 in the form used below.** A constructible subset of a spectral space contained
in a set stable under specialization has its closure contained there too: the subset is closed in
the constructible topology, so every point of its closure is a specialization of one of its
points. -/
@[sga "3 XV 3.3" "special case"]
private theorem exists_isClosed_of_isConstructible_subset {Y : Type*} [TopologicalSpace Y]
    [SpectralSpace Y] {E S : Set Y} (hE : StableUnderSpecialization E)
    (hS : Topology.IsConstructible S) (hSE : S ⊆ E) :
    ∃ Z : Set Y, IsClosed Z ∧ Z ⊆ E ∧ S ⊆ Z := by
  refine ⟨closure S, isClosed_closure, fun x hx => ?_, subset_closure⟩
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology
    (SpectralSubset.isClosed_constructibleTopology_of_isConstructible S hS) hx
  exact hE hyx (hSE hy)

/-- The underlying space of a Noetherian scheme is spectral. -/
private theorem spectralSpace_of_isNoetherian (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.obj] : SpectralSpace X.obj := by
  have hNoeth := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  let : IsLocallyNoetherian X.obj := hNoeth.1
  let : CompactSpace X.obj := hNoeth.2
  let : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  let : TopologicalSpace.NoetherianSpace X.obj := inferInstance
  exact { toT0Space := inferInstance
          toCompactSpace := inferInstance
          toQuasiSober := inferInstance
          toQuasiSeparatedSpace := inferInstance
          toPrespectralSpace := inferInstance }

/-! ### Torsion abelian sheaves -/

section Abelian

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  (X : B.Scheme)

/-- **Stacks 03SA (2) as a hypothesis.** Every torsion abelian sheaf on the small étale site of
`X` is a filtered colimit of constructible abelian sheaves, in the diagram-and-colimit-cocone
spelling of the library's other two parts of Stacks 03SA.

This holds on every quasi-compact and quasi-separated `X`: it is the library's Stacks 03SA (2),
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`, stated at the
same local notion of torsion. -/
public def TorsionAbelianSheavesAreFilteredColimitsOfConstructibles : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1},
    Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F →
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i)

/-- **Stacks 0F0N, part (1).** Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under
specialization. A torsion abelian sheaf `F` on the small étale site of `X` whose support is
contained in `E` is a filtered colimit of constructible abelian sheaves, each of whose supports
is contained in a closed subset of `E`.

This is the source's own proof. Write `F` as a filtered colimit of constructible abelian sheaves
`F i` by Stacks 03SA (2), and replace each `F i` by the image `F' i` of `F i ⟶ F`. The images
again form a filtered colimit with vertex `F`, because each leg factors through its image by an
epimorphism; each `F' i` is constructible, being a quotient of `F i`, by Stacks 09BH (2); and the
support of `F' i` lies in the support of `F`, hence in `E`, because `F' i` is a subsheaf of `F`
and a geometric stalk is left exact. That support is constructible by Stacks 09YS (2), so
Stacks 0903 puts its closure inside `E` as well, and the closure is the required closed set.

Part (1) without the hypothesis is
`exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support_of_torsion`. -/
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_isClosed_support
    [IsNoetherian X.obj]
    (h03SA : TorsionAbelianSheavesAreFilteredColimitsOfConstructibles B X)
    (E : Set X.obj) (hE : StableUnderSpecialization E)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (SmallEtale.topology B X.obj X.property) F)
    (hsupp : supportSheaf B X.obj X.property F ⊆ E) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i) ∧
          ∃ Z : Set X.obj, IsClosed Z ∧ Z ⊆ E ∧
            supportSheaf B X.obj X.property (D.obj i) ⊆ Z := by
  let : SpectralSpace X.obj := spectralSpace_of_isNoetherian B X
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ := h03SA F hF
  refine ⟨I, hI, hfilt, imageDiagram D ι, (imageDiagramCocone D ι).ι,
    ⟨imageDiagramCocone_isColimit D ι hcolim⟩, fun i => ?_⟩
  have hconstr : IsConstructibleAbelianSheaf B X (Abelian.image (ι.app i)) :=
    isConstructibleAbelianSheaf_of_epi B X
      (smallEtaleUnderlyingSetCommutes B X)
      (representableIsConstructibleSetSheaf B X)
      (hasFiniteRepresentableCover B X)
      (Abelian.factorThruImage (ι.app i)) (hD i)
  have hsub : supportSheaf B X.obj X.property (Abelian.image (ι.app i)) ⊆ E :=
    (supportSheaf_subset_of_mono B X (Abelian.image (ι.app i)) F
      (Abelian.image.ι (ι.app i))).trans hsupp
  obtain ⟨Z, hZclosed, hZE, hZsupp⟩ := exists_isClosed_of_isConstructible_subset hE
    (isConstructible_supportSheaf B X (Abelian.image (ι.app i)) hconstr) hsub
  exact ⟨hconstr, Z, hZclosed, hZE, hZsupp⟩

end Abelian

/-! ### Sheaves of modules over a Noetherian ring -/

section Modules

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ]

/-- The support of a sheaf of `Λ`-modules on the small étale site of `X`: the points of `X` at
which some geometric stalk is nonzero. This is the set whose constructibility, for a
constructible sheaf, is the library's Stacks 09YS (3),
`AlgebraicGeometry.isConstructible_support_moduleSheaf`. -/
public def supportModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) : Set X.obj :=
  {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
    ¬ IsZero (etaleStalk B X.obj X.property t F.obj)}

omit [IsNoetherianRing Λ] in
/-- **The support of a subsheaf of `Λ`-modules is contained in the support of the ambient
sheaf**, by the same left exactness of the geometric stalk as in the abelian case. -/
private theorem supportModuleSheaf_subset_of_mono
    (G F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (i : G ⟶ F) [Mono i] :
    supportModuleSheaf B X Λ G ⊆ supportModuleSheaf B X Λ F := by
  rintro x ⟨p, hp, hn⟩
  let : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1} Λ)
  exact ⟨p, hp, fun hzero => hn (isZero_etaleStalk_of_mono B X p _ G F i hzero)⟩

/-- **Stacks 0F0N, part (2).** Let `X` be a Noetherian scheme, let `Λ` be a Noetherian ring and
let `E ⊆ X` be stable under specialization. A sheaf of `Λ`-modules `F` on the small étale site of
`X` whose support is contained in `E` is a filtered colimit of constructible sheaves of
`Λ`-modules, each of whose supports is contained in a closed subset of `E`.

The source says of this part only that it is "exactly the same" as part (1), and so it is: write
`F` as a filtered colimit of constructible sheaves of `Λ`-modules by Stacks 03SA (3) — which is
in the library — replace each term by the image of its map to `F`, and run the same three steps,
with Stacks 09BH (3) in place of Stacks 09BH (2) and Stacks 09YS (3) in place of
Stacks 09YS (2).

Stacks 03SA (3) enters as the unconditional
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`, so neither
Stacks 093C in the shriek spelling nor the sheaves-of-modules case of Stacks 03S8 has to be
supplied here. Stacks 09BH (3) enters through
`AlgebraicGeometry.isConstructibleModuleSheaf_forall_epi`, whose own geometric step is
`AlgebraicGeometry.finiteTypeLocallyConstantSubsheavesAreConstructible`. So this statement
assumes nothing. -/
@[stacks 0F0N "part (2); Stacks 03SA (3), Stacks 093C, Stacks 03S8 for sheaves of modules, \
  Stacks 09BH (3), Stacks 09YS (3), Stacks 0903, Stacks 095E, Stacks 09YR and \
  Stacks 03RZ (3) are all discharged from the library"]
public theorem exists_isFilteredColimit_isConstructibleModuleSheaf_isClosed_support
    [IsNoetherian X.obj]
    (E : Set X.obj) (hE : StableUnderSpecialization E)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hsupp : supportModuleSheaf B X Λ F ⊆ E) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleModuleSheaf B X Λ (D.obj i) ∧
          ∃ Z : Set X.obj, IsClosed Z ∧ Z ⊆ E ∧ supportModuleSheaf B X Λ (D.obj i) ⊆ Z := by
  let : SpectralSpace X.obj := spectralSpace_of_isNoetherian B X
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs B X Λ F
  refine ⟨I, hI, hfilt, imageDiagram D ι, (imageDiagramCocone D ι).ι,
    ⟨imageDiagramCocone_isColimit D ι hcolim⟩, fun i => ?_⟩
  have hconstr : IsConstructibleModuleSheaf B X Λ (Abelian.image (ι.app i)) :=
    isConstructibleModuleSheaf_forall_epi B X Λ
      (finiteTypeLocallyConstantSubsheavesAreConstructible B X Λ) _ _
      (Abelian.factorThruImage (ι.app i)) inferInstance (hD i)
  have hsub : supportModuleSheaf B X Λ (Abelian.image (ι.app i)) ⊆ E :=
    (supportModuleSheaf_subset_of_mono B X Λ (Abelian.image (ι.app i)) F
      (Abelian.image.ι (ι.app i))).trans hsupp
  obtain ⟨Z, hZclosed, hZE, hZsupp⟩ := exists_isClosed_of_isConstructible_subset hE
    (isConstructible_support_moduleSheaf.{u + 1, u, u + 1} B X Λ
      (Abelian.image (ι.app i)) hconstr) hsub
  exact ⟨hconstr, Z, hZclosed, hZE, hZsupp⟩

end Modules

end AlgebraicGeometry

end
