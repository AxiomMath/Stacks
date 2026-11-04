module

public import StacksFrontier.AlgebraicGeometry.FinitelyPresentableComposition.Directed
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SubalgebraJoinFiniteType

/-!
# An integral quasi-coherent algebra on an algebraic space as a colimit of finite algebras

Let `S` be a scheme, let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and
let `𝒜` be an integral quasi-coherent `𝒪_Y`-algebra. Then the finite quasi-coherent
`𝒪_Y`-subalgebras of `𝒜` form a filtered category whose colimit is `𝒜`, and `𝒜` is a directed
colimit of quasi-coherent `𝒪_Y`-algebras which are finite and of finite presentation.

The colimit statements are proved under a hypothesis `hgen`: every section of `𝒜` over an affine
étale chart `U` of `Y` is a section over `U` of some finite quasi-coherent subalgebra of `𝒜`. The
finite and finitely presented colimit is proved under two further hypotheses: `hstage`, that every
finite quasi-coherent algebra on `Y` is a filtered colimit of quotients of one algebra sheaf by
ideal sheaves with finitely presented quotients, one of them integral; and `hpres`, that every
finite and finitely presented quasi-coherent algebra is finitely presentable along every filtered
colimit cocone of quasi-coherent algebras.

## Main definitions

* `AlgebraicGeometry.Space.finiteSubalgebraQcohDiagram`: The diagram of the finite quasi-coherent
  subalgebras of a quasi-coherent algebra, in the category of quasi-coherent algebras.
* `AlgebraicGeometry.Space.finiteSubalgebraQcohCocone`: The cocone of the inclusions of these
  subalgebras, in the category of quasi-coherent algebras.

## Main results

* `AlgebraicGeometry.Space.isFiltered_finiteSubalgebra`: The finite quasi-coherent subalgebras of
  an integral quasi-coherent algebra form a filtered category.
* `AlgebraicGeometry.Space.nonempty_isColimit_finiteSubalgebraCocone`: Under `hgen`, an integral
  quasi-coherent algebra is the colimit of its finite quasi-coherent subalgebras.
* `AlgebraicGeometry.Space.nonempty_isColimit_finiteSubalgebraQcohCocone`: The same colimit, in the
  category of quasi-coherent algebras.
* `AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation`: Under `hgen`, `hstage`
  and `hpres`, an integral quasi-coherent algebra is a directed colimit of finite and finitely
  presented quasi-coherent algebras.

## References

* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The finite quasi-coherent subalgebras of an integral quasi-coherent sheaf of commutative
`𝒪_Y`-algebras on an algebraic space `Y` form a filtered category. -/
@[stacks 082C "part (1), the directedness assertion, and with no hypothesis beyond \
quasi-coherence and integrality of the algebra: neither quasi-compactness nor quasi-separatedness \
of the space is used. The colimit assertion of part (1) is \
AlgebraicGeometry.Space.nonempty_isColimit_finiteSubalgebraCocone and part (2) is \
AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation; those two name their own \
restrictions, this one has none"]
theorem isFiltered_finiteSubalgebra (Y : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hqcoh : A.IsQuasicoherent)
    (hint : A.IsIntegral) :
    IsFiltered (FiniteSubalgebra B S hS Y.1 Y.2 A) :=
  isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra' B S hS Y.1 Y.2 A hint
    (isFiltered_finiteTypeSubalgebra Y A hqcoh)

/-- An integral quasi-coherent sheaf of commutative `𝒪_Y`-algebras `A` on a quasi-compact and
quasi-separated algebraic space `Y` is the colimit of the cocone of the inclusions of its finite
quasi-coherent subalgebras, provided (`hgen`) every section of `A` over an affine étale chart of
`Y` lies in the image of one finite quasi-coherent subalgebra of `A`. -/
@[stacks 082C "part (1), the colimit assertion, over the carried input hgen: for every affine \
etale chart U of the space and every section x of the algebra over U there is a finite \
quasi-coherent subalgebra of the algebra, on the whole space, having x among its sections over U. \
hgen is the algebraic-space analogue of what the scheme-level development derives from Stacks \
01PF, namely \
Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.exists_finiteTypeSubalgebra_section, and it \
is asked only AT THE SPACE AND THE ALGEBRA OF THE STATEMENT. It replaces the colimit assertion of \
Stacks 082B, which is blocked by the source's own route on Stacks 07SU through Stacks 0829 and \
Stacks 07V9, and is strictly weaker than it: hgen mentions no cocone, no colimit and no index, and \
quantifies only over sections over single affine etale charts. Everything else is proved: \
directedness of the index is AlgebraicGeometry.Space.isFiltered_finiteSubalgebra, which has no \
restriction at all, sectionwise injectivity of the legs is \
AlgebraicGeometry.Space.AlgebraSheaf.injective_subobject_arrow_app, and the passage from sections \
over the affine etale charts to the colimit property is \
AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_of_affineChartSections_of_injective. The \
identification of the finite with the finite type quasi-coherent subalgebras over an integral \
algebra, which is Algebra Lemma 10.36.5 on the affine etale charts, is proved as \
AlgebraicGeometry.Space.isQuasicoherentAndIsFinite_eq_isQuasicoherentAndIsFiniteType'"]
theorem nonempty_isColimit_finiteSubalgebraCocone (Y : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hqcoh : A.IsQuasicoherent) (hint : A.IsIntegral)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hgen : IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      ∀ U : SmallEtale B S hS Y.1,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : A.right.obj.obj (op U),
          ∃ C : FiniteSubalgebra B S hS Y.1 Y.2 A,
            x ∈ Set.range ((C.obj.arrow.right.hom.app (op U)).hom)) :
    Nonempty (IsColimit (finiteSubalgebraCocone B S hS Y.1 Y.2 A)) := by
  have := isFiltered_finiteSubalgebra B S hS Y A hqcoh hint
  refine AlgebraSheaf.nonempty_isColimit_of_affineChartSections_of_injective
    (finiteSubalgebraCocone B S hS Y.1 Y.2 A) (fun U _ C => ?_) (fun U hU x => ?_)
  · rw [AlgebraSheaf.chartSectionsFunctor_map]
    exact AlgebraSheaf.injective_subobject_arrow_app C.obj (op U)
  · obtain ⟨C, y, hy⟩ := hgen hqc hqs U hU x
    exact ⟨C, y, by rwa [AlgebraSheaf.chartSectionsFunctor_map]⟩

/-! ### The finite subalgebras in the category of quasi-coherent algebras -/

/-- The diagram of the finite quasi-coherent subalgebras of a quasi-coherent algebra sheaf, read in
the quasi-coherent algebras. -/
noncomputable def finiteSubalgebraQcohDiagram (Y : AlgebraicSpaces B S hS)
    (A : QuasicoherentAlgebra B S hS Y) :
    FiniteSubalgebra B S hS Y.1 Y.2 A.obj ⥤ QuasicoherentAlgebra B S hS Y :=
  ObjectProperty.lift _ (finiteSubalgebraDiagram B S hS Y.1 Y.2 A.obj) fun C => C.property.1

/-- The cocone of the inclusions of the finite quasi-coherent subalgebras of a quasi-coherent
algebra sheaf, read in the quasi-coherent algebras. -/
noncomputable def finiteSubalgebraQcohCocone (Y : AlgebraicSpaces B S hS)
    (A : QuasicoherentAlgebra B S hS Y) :
    finiteSubalgebraQcohDiagram B S hS Y A ⟶ (Functor.const _).obj A where
  app C := ObjectProperty.homMk C.obj.arrow
  naturality _ _ f :=
    ObjectProperty.hom_ext _ ((Subobject.underlying_arrow f.hom).trans (Category.comp_id _).symm)

/-- Under the hypothesis `hgen` of `nonempty_isColimit_finiteSubalgebraCocone`, the cocone of the
inclusions of the finite quasi-coherent subalgebras of an integral quasi-coherent algebra `A` is
colimiting in `AlgebraicGeometry.Space.QuasicoherentAlgebra B S hS Y`. -/
theorem nonempty_isColimit_finiteSubalgebraQcohCocone (Y : AlgebraicSpaces B S hS)
    (A : QuasicoherentAlgebra B S hS Y) (hint : A.obj.IsIntegral)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hgen : IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      ∀ U : SmallEtale B S hS Y.1,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : A.obj.right.obj.obj (op U),
          ∃ C : FiniteSubalgebra B S hS Y.1 Y.2 A.obj,
            x ∈ Set.range ((C.obj.arrow.right.hom.app (op U)).hom)) :
    Nonempty (IsColimit (Cocone.mk A (finiteSubalgebraQcohCocone B S hS Y A))) := by
  have := isFiltered_finiteSubalgebra B S hS Y A.obj A.property hint
  exact nonempty_isColimit_quasicoherentAlgebra_of_affineChartSections
    (Cocone.mk A (finiteSubalgebraQcohCocone B S hS Y A)) (fun U hU x => hgen hqc hqs U hU x)
    fun U _ C x y hxy =>
      ⟨C, 𝟙 C, by rw [AlgebraSheaf.injective_subobject_arrow_app C.obj (op U) hxy]⟩

/-- An integral quasi-coherent sheaf of commutative `𝒪_Y`-algebras on a quasi-compact and
quasi-separated algebraic space `Y` is the colimit of a system, indexed by a nonempty directed
preorder, of quasi-coherent `𝒪_Y`-algebras each of which is finite and of finite presentation,
provided `hgen` (as in `nonempty_isColimit_finiteSubalgebraCocone`), `hstage` (every finite
quasi-coherent algebra on `Y` is a filtered colimit of finitely presented quotients of an algebra
sheaf, one of them integral) and `hpres` (every finite and finitely presented quasi-coherent
algebra is finitely presentable along every filtered colimit cocone of quasi-coherent algebras). -/
@[stacks 082C "part (2), over three carried inputs. (a) hgen, the same input as in \
AlgebraicGeometry.Space.nonempty_isColimit_finiteSubalgebraCocone: every section of the algebra \
over an affine etale chart lies in the image of one finite quasi-coherent subalgebra on the whole \
space. Part (1) is PROVED from it here and is not assumed. (b) hstage, the carried input of \
Stacks 086Z itself — see the module documentation of \
StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem for what it says — \
asked at every finite quasi-coherent algebra on the space rather than at one; Stacks 086Z is not \
restated, the theorem \
AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective is \
called, so the finiteness, the finite presentation and the directedness of every inner system are \
that theorem's and not assumed here. (c) hpres, presentability of a finite and finitely presented \
quasi-coherent algebra ALONG THE TWO SYSTEMS' OWN COCONES, which is the analogue for algebraic \
spaces of the input the source takes from Cohomology of Spaces Lemma 69.5.3 and is weaker both \
than that lemma and than CategoryTheory.IsFinitelyPresentable of the stages: nothing is asked \
about any filtered colimit other than the two being spliced. On schemes the corresponding \
statement is a theorem, \
Stacks.AlgebraicGeometry.Tag0817Presentable.presentableAlong_of_isFinitePresentation, proved by \
carrying Stacks 01ZC across the relative spectrum of Stacks 01SA; for algebraic spaces the \
relative spectrum of Stacks 081W and the limit-preserving criterion \
AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving of Stacks 04AK are proved \
but the passage from a colimit of algebra sheaves to a limit of algebraic spaces affine over the \
base is not, so hpres is not proved. What is proved on top of the three: part (1) from hgen, \
including its directedness which has no restriction, the lifting of each inner index from Type u \
to the morphism universe of the quasi-coherent algebras along CategoryTheory.AsSmall, the splice \
itself, and that every stage of the resulting directed system is finite and of finite \
presentation. No declaration in this file assumes any assertion of Stacks 082C"]
theorem exists_directed_isFinite_isFinitePresentation (Y : AlgebraicSpaces B S hS)
    (A : QuasicoherentAlgebra B S hS Y) (hint : A.obj.IsIntegral)
    (hqc : IsQuasiCompactSpace B S hS Y.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj)
    (hgen : IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      ∀ U : SmallEtale B S hS Y.1,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : A.obj.right.obj.obj (op U),
          ∃ C : FiniteSubalgebra B S hS Y.1 Y.2 A.obj,
            x ∈ Set.range ((C.obj.arrow.right.hom.app (op U)).hom))
    (hstage : ∀ C : QuasicoherentAlgebra B S hS Y,
      IsQuasiCompactSpace B S hS Y.obj →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.obj →
      C.obj.IsFinite →
        ∃ (ℬ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (f : ℬ ⟶ C.obj) (J : Type u)
          (inst : SmallCategory J),
          let _ := inst
          ∃ (_ : IsFiltered J) (ι : J → ℬ.IdealSheaf)
            (hι : ∀ j j' : J, (j ⟶ j') → ι j ≤ ι j')
            (hkill : ∀ (j : J) (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : ℬ.right.obj.obj U),
              a ∈ (ι j).obj U → (f.right.hom.app U).hom a = 0)
            (hqcoh : ∀ j, (ℬ.idealQuotient (ι j)).IsQuasicoherent),
            (∀ j, (ℬ.idealQuotient (ι j)).IsFinitePresentation) ∧
            (∃ j, (ℬ.idealQuotient (ι j)).IsIntegral) ∧
            Nonempty (IsColimit (Cocone.mk C
              (idealQuotientQcohCocone ℬ ι hι C f hkill hqcoh))))
    (hpres : ∀ T : QuasicoherentAlgebra B S hS Y, T.obj.IsFinite → T.obj.IsFinitePresentation →
      ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
        (Φ : J ⥤ QuasicoherentAlgebra B S hS Y) (c : Cocone Φ), IsColimit c →
        Stacks.FinitelyPresentableComposition.PresentableAlong T c) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ QuasicoherentAlgebra B S hS Y) (φ : D ⟶ (Functor.const I).obj A),
      Nonempty (IsColimit (Cocone.mk A φ)) ∧
      ∀ i, (D.obj i).obj.IsFinite ∧ (D.obj i).obj.IsFinitePresentation := by
  have := isFiltered_finiteSubalgebra B S hS Y A.obj A.property hint
  obtain ⟨ht⟩ := nonempty_isColimit_finiteSubalgebraQcohCocone B S hS Y A hint hqc hqs hgen
  choose K instK hKne hKdir D' φ' hcol' hobj' _hmor' using
    fun C : FiniteSubalgebra B S hS Y.1 Y.2 A.obj =>
      exists_directed_isFinite_isFinitePresentation_locallySurjective B S hS Y
        ((finiteSubalgebraQcohDiagram B S hS Y A).obj C) hqc hqs C.property.2
        (hstage ((finiteSubalgebraQcohDiagram B S hS Y A).obj C))
  let _ : ∀ C, IsFiltered (AsSmall.{u + 1} (K C)) :=
    fun C => IsFiltered.of_equivalence (AsSmall.equiv (C := K C))
  let E : ∀ C, AsSmall.{u + 1} (K C) ⥤ QuasicoherentAlgebra B S hS Y :=
    fun C => (AsSmall.equiv (C := K C)).symm.functor ⋙ D' C
  let s : ∀ C, E C ⟶ (Functor.const (AsSmall.{u + 1} (K C))).obj
      ((finiteSubalgebraQcohDiagram B S hS Y A).obj C) :=
    fun C => Functor.whiskerLeft (AsSmall.equiv (C := K C)).symm.functor (φ' C)
  have hs : ∀ C, IsColimit (Cocone.mk ((finiteSubalgebraQcohDiagram B S hS Y A).obj C) (s C)) :=
    fun C => (hcol' C).some.whiskerEquivalence (AsSmall.equiv (C := K C)).symm
  have hstages : ∀ (C : FiniteSubalgebra B S hS Y.1 Y.2 A.obj) (k : AsSmall.{u + 1} (K C)),
      ((E C).obj k).obj.IsFinite ∧ ((E C).obj k).obj.IsFinitePresentation :=
    fun C k => hobj' C ((AsSmall.equiv (C := K C)).symm.functor.obj k)
  obtain ⟨I, instI, hne, hdir, F, σ, hcolF, hP⟩ :=
    Stacks.FinitelyPresentableComposition.exists_directed_index_of_twoStage
      (K := fun C => AsSmall.{u + 1} (K C)) (E := E)
      (finiteSubalgebraQcohCocone B S hS Y A) s ht hs
      (fun C k => ⟨hpres _ (hstages C k).1 (hstages C k).2 _ _ _ ht,
        fun C' => hpres _ (hstages C k).1 (hstages C k).2 _ _ _ (hs C')⟩)
      (fun T => T.obj.IsFinite ∧ T.obj.IsFinitePresentation) hstages
  exact ⟨I, instI, hne, hdir, F, σ, ⟨hcolF⟩, hP⟩

end AlgebraicGeometry.Space

end
