module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates

/-!
# Transport of a base change map along a morphism of squares of adjunctions

Let `Da ⊣ ra`, `Da' ⊣ ra'` be adjunctions forming, with `Db`, `Db'` and identifications
`egr : Db ⋙ Da' ≅ Dc`, `efr : Da ⋙ Db' ≅ Dc`, a square (for instance derived extension and
restriction of scalars along a commutative square of rings), and let `Lf ⊣ Rf`, `Lf' ⊣ Rf'`,
`Lg`, `Lg'`, `eg`, `ef` be a second square (for instance derived pullback and direct image along
a commutative square of algebraic spaces).  Let functors `Φ` from the corners of the first square
to those of the second intertwine the left adjoints through isomorphisms `β`, compatibly with the
identifications of the two composites around the squares (`hhex`).

Then the base change map of the second square at `Φ M`, read through the transposes `γ` of the
`β`, is `Φ` of the base change map of the first square at `M`.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.transportUnit`: the map `Φ (ra M) ⟶ Rf (Φ M)` transpose to
  `β` followed by `Φ` of the counit of `Da ⊣ ra`.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_transport`
* `Stacks.CategoryTheory.BaseChange.map_transport_of_central`: the same when the compatibility
  holds only up to an automorphism of the identity functor of the last corner.
* `Stacks.CategoryTheory.BaseChange.app_eq_map_of_unit`: a 2-cell `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` with the
  unit equation of the mate is the base change map.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

section Transport

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  {Da : C₁ ⥤ D₁} {ra : D₁ ⥤ C₁} {Lf : C₂ ⥤ D₂} {Rf : D₂ ⥤ C₂}
  (adja : Da ⊣ ra) (adjf : Lf ⊣ Rf) (ΦR : C₁ ⥤ C₂) (ΦA : D₁ ⥤ D₂)
  (βf : ΦR ⋙ Lf ≅ Da ⋙ ΦA)

/-- The map `Φ_R (ra M) ⟶ Rf (Φ_A M)`: the transpose under `Lf ⊣ Rf` of `β` at `ra M` followed
by `Φ_A` of the counit of `Da ⊣ ra` at `M`. -/
def transportUnit (M : D₁) : ΦR.obj (ra.obj M) ⟶ Rf.obj (ΦA.obj M) :=
  adjf.homEquiv _ _ (βf.hom.app (ra.obj M) ≫ ΦA.map (adja.counit.app M))

theorem homEquiv_symm_transportUnit (M : D₁) :
    (adjf.homEquiv _ _).symm (transportUnit adja adjf ΦR ΦA βf M) =
      βf.hom.app (ra.obj M) ≫ ΦA.map (adja.counit.app M) :=
  Equiv.symm_apply_apply _ _

/-- `transportUnit` is natural in the object. -/
theorem transportUnit_naturality {M M' : D₁} (φ : M ⟶ M') :
    ΦR.map (ra.map φ) ≫ transportUnit adja adjf ΦR ΦA βf M' =
      transportUnit adja adjf ΦR ΦA βf M ≫ Rf.map (ΦA.map φ) := by
  rw [transportUnit, transportUnit, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h₁ := βf.hom.naturality (ra.map φ)
  have h₂ := adja.counit.naturality φ
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at h₁ h₂
  rw [reassoc_of% h₁, ← ΦA.map_comp, h₂, ΦA.map_comp, Category.assoc]

/-- **`ΓR` of the transported unit.**  For adjunctions `ΦR ⊣ ΓR` and `ΦA ⊣ ΓA`, the unit of
`ΦR ⊣ ΓR` at `ra M` followed by `ΓR` of `transportUnit` is `ra` of the unit of `ΦA ⊣ ΓA` at `M`
followed by the conjugate of `βf` at `ΦA M`. -/
theorem unit_comp_map_transportUnit {ΓR : C₂ ⥤ C₁} {ΓA : D₂ ⥤ D₁} (adjΦR : ΦR ⊣ ΓR)
    (adjΦA : ΦA ⊣ ΓA) (M : D₁) :
    adjΦR.unit.app (ra.obj M) ≫ ΓR.map (transportUnit adja adjf ΦR ΦA βf M) =
      ra.map (adjΦA.unit.app M) ≫
        (conjugateEquiv (adja.comp adjΦA) (adjΦR.comp adjf) βf.hom).app (ΦA.obj M) := by
  have hu := unit_conjugateEquiv (adja.comp adjΦA) (adjΦR.comp adjf) βf.hom (ra.obj M)
  have hn := (conjugateEquiv (adja.comp adjΦA) (adjΦR.comp adjf) βf.hom).naturality
    (ΦA.map (adja.counit.app M))
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map,
    Category.assoc] at hu hn
  have hη := adjΦA.unit.naturality (adja.counit.app M)
  simp only [Functor.id_map, Functor.comp_map] at hη
  rw [transportUnit, Adjunction.homEquiv_unit, ΓR.map_comp, Functor.map_comp, Functor.map_comp]
  have hη' : adja.counit.app M ≫ adjΦA.unit.app M =
      adjΦA.unit.app (Da.obj (ra.obj M)) ≫ ΓA.map (ΦA.map (adja.counit.app M)) := hη
  have hn' : ra.map (ΓA.map (ΦA.map (adja.counit.app M))) ≫
      (conjugateEquiv (adja.comp adjΦA) (adjΦR.comp adjf) βf.hom).app (ΦA.obj M) =
    (conjugateEquiv (adja.comp adjΦA) (adjΦR.comp adjf) βf.hom).app (ΦA.obj (Da.obj (ra.obj M))) ≫
      ΓR.map (Rf.map (ΦA.map (adja.counit.app M))) := hn
  rw [← reassoc_of% hu, ← hn', ← ra.map_comp_assoc, ← hη', ra.map_comp, Category.assoc,
    Adjunction.right_triangle_components_assoc]

/-- If the units of `ΦR ⊣ ΓR` at `ra M` and of `ΦA ⊣ ΓA` at `M` are invertible, then so is
`ΓR` of `transportUnit` at `M`. -/
theorem isIso_map_transportUnit {ΓR : C₂ ⥤ C₁} {ΓA : D₂ ⥤ D₁} (adjΦR : ΦR ⊣ ΓR)
    (adjΦA : ΦA ⊣ ΓA) (M : D₁) [IsIso (adjΦR.unit.app (ra.obj M))]
    [IsIso (adjΦA.unit.app M)] :
    IsIso (ΓR.map (transportUnit adja adjf ΦR ΦA βf M)) := by
  have h := unit_comp_map_transportUnit adja adjf ΦR ΦA βf adjΦR adjΦA M
  have : IsIso (adjΦR.unit.app (ra.obj M) ≫ ΓR.map (transportUnit adja adjf ΦR ΦA βf M)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (adjΦR.unit.app (ra.obj M)) _

end Transport

section Square

variable {CR CA CR' CA' DV DU DW DP : Type*} [Category CR] [Category CA] [Category CR']
  [Category CA'] [Category DV] [Category DU] [Category DW] [Category DP]
  {Da : CR ⥤ CA} {ra : CA ⥤ CR} {Da' : CR' ⥤ CA'} {ra' : CA' ⥤ CR'} {Db : CR ⥤ CR'}
  {Db' : CA ⥤ CA'} {Dc : CR ⥤ CA'}
  (adja : Da ⊣ ra) (adja' : Da' ⊣ ra') (egr : Db ⋙ Da' ≅ Dc) (efr : Da ⋙ Db' ≅ Dc)
  {Lf : DV ⥤ DU} {Rf : DU ⥤ DV} {Lf' : DW ⥤ DP} {Rf' : DP ⥤ DW} {Lg : DV ⥤ DW}
  {Lg' : DU ⥤ DP} {Lc : DV ⥤ DP}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (ΦR : CR ⥤ DV) (ΦA : CA ⥤ DU) (ΦR' : CR' ⥤ DW) (ΦA' : CA' ⥤ DP)
  (βf : ΦR ⋙ Lf ≅ Da ⋙ ΦA) (βf' : ΦR' ⋙ Lf' ≅ Da' ⋙ ΦA')
  (βg : ΦR ⋙ Lg ≅ Db ⋙ ΦR') (βg' : ΦA ⋙ Lg' ≅ Db' ⋙ ΦA')

/-- **Transport of the base change map.**  If the `β` are compatible with the identifications of
the two composites around the squares (`hhex`), then `Lg` of the transpose of `βf` followed by
the base change map of the second square at `Φ_A M` is `βg`, then `Φ_{R'}` of the base change map
of the first square at `M`, then the transpose of `βf'` and `Rf'` of `βg'⁻¹`. -/
theorem map_transport
    (hhex : ∀ N : CR, Lf'.map (βg.hom.app N) ≫ βf'.hom.app (Db.obj N) ≫
        ΦA'.map (egr.hom.app N ≫ efr.inv.app N) =
      eg.hom.app (ΦR.obj N) ≫ ef.inv.app (ΦR.obj N) ≫ Lg'.map (βf.hom.app N) ≫
        βg'.hom.app (Da.obj N))
    (M : CA) :
    Lg.map (transportUnit adja adjf ΦR ΦA βf M) ≫ map adjf adjf' eg ef (ΦA.obj M) =
      βg.hom.app (ra.obj M) ≫ ΦR'.map (map adja adja' egr efr M) ≫
        transportUnit adja' adjf' ΦR' ΦA' βf' (Db'.obj M) ≫ Rf'.map (βg'.inv.app M) := by
  apply (adjf'.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map_comp_map, homEquiv_symm_transportUnit,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, homEquiv_symm_transportUnit]
  have hr := homEquiv_symm_map adja adja' egr efr M
  rw [Adjunction.homEquiv_counit] at hr
  have h₁ := βf'.hom.naturality (map adja adja' egr efr M)
  have h₂ := βg'.hom.naturality (adja.counit.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% h₁, ← ΦA'.map_comp_assoc, hr]
  simp only [Functor.map_comp, Category.assoc]
  have hh := hhex (ra.obj M)
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [reassoc_of% hh, ← reassoc_of% h₂, Iso.hom_inv_id_app]
  exact (congrArg (fun t => eg.hom.app (ΦR.obj (ra.obj M)) ≫ ef.inv.app (ΦR.obj (ra.obj M)) ≫
    Lg'.map (βf.hom.app (ra.obj M)) ≫ t)
    (Category.comp_id (Lg'.map (ΦA.map (adja.counit.app M))))).symm

/-- **Transport of the base change map up to a central automorphism.**  If the `β` are
compatible with the identifications of the composites around the squares only up to `Φ_{A'}` of
an automorphism `t` of the identity functor of the corner `CA'` (`hhex`), then the base change map
of the second square at `Φ_A M` is still `Φ_{R'}` of the base change map of the first square,
read through the transposes of the `β`, with `βg'` corrected by `t`. -/
theorem map_transport_of_central (t : 𝟭 CA' ≅ 𝟭 CA')
    (hhex : ∀ N : CR, Lf'.map (βg.hom.app N) ≫ βf'.hom.app (Db.obj N) ≫
        ΦA'.map (egr.hom.app N ≫ efr.inv.app N) =
      eg.hom.app (ΦR.obj N) ≫ ef.inv.app (ΦR.obj N) ≫ Lg'.map (βf.hom.app N) ≫
        βg'.hom.app (Da.obj N) ≫ ΦA'.map (t.hom.app (Db'.obj (Da.obj N))))
    (M : CA) :
    Lg.map (transportUnit adja adjf ΦR ΦA βf M) ≫ map adjf adjf' eg ef (ΦA.obj M) =
      βg.hom.app (ra.obj M) ≫ ΦR'.map (map adja adja' egr efr M) ≫
        transportUnit adja' adjf' ΦR' ΦA' βf' (Db'.obj M) ≫
          Rf'.map (ΦA'.map (t.inv.app (Db'.obj M)) ≫ βg'.inv.app M) :=
  map_transport adja adja' egr efr adjf adjf' eg ef ΦR ΦA ΦR' ΦA' βf βf' βg
    (βg' ≪≫ Functor.isoWhiskerLeft Db' (Functor.isoWhiskerRight t ΦA')) hhex M

/-- The compatibility `hhex` up to a central automorphism, from its form with the second
identification moved to the right. -/
theorem hhex_of_comp_eq (t : 𝟭 CA' ≅ 𝟭 CA')
    (h : ∀ N : CR, Lf'.map (βg.hom.app N) ≫ βf'.hom.app (Db.obj N) ≫ ΦA'.map (egr.hom.app N) =
      eg.hom.app (ΦR.obj N) ≫ ef.inv.app (ΦR.obj N) ≫ Lg'.map (βf.hom.app N) ≫
        βg'.hom.app (Da.obj N) ≫ ΦA'.map (efr.hom.app N) ≫ ΦA'.map (t.hom.app (Dc.obj N)))
    (N : CR) :
    Lf'.map (βg.hom.app N) ≫ βf'.hom.app (Db.obj N) ≫
        ΦA'.map (egr.hom.app N ≫ efr.inv.app N) =
      eg.hom.app (ΦR.obj N) ≫ ef.inv.app (ΦR.obj N) ≫ Lg'.map (βf.hom.app N) ≫
        βg'.hom.app (Da.obj N) ≫ ΦA'.map (t.hom.app (Db'.obj (Da.obj N))) := by
  have hn : t.hom.app (Dc.obj N) ≫ efr.inv.app N = efr.inv.app N ≫ t.hom.app (Db'.obj (Da.obj N)) :=
    (t.hom.naturality (efr.inv.app N)).symm
  have h' := congrArg (· ≫ ΦA'.map (efr.inv.app N)) (h N)
  simp only [Category.assoc] at h'
  rw [ΦA'.map_comp, h']
  simp only [← ΦA'.map_comp, hn, Iso.hom_inv_id_app_assoc]

/-- **Invertibility transported along the squares.**  Under the hypotheses of
`map_transport_of_central`, if the transposed units are invertible and `Φ_{R'}` reflects
isomorphisms, the base change map of the second square at `Φ_A M` followed by `Rf'` of `βg'`
and of `Φ_{A'} φ` is invertible exactly when the base change map of the first square at `M`
followed by `ra' φ` is. -/
theorem isIso_map_comp_iff_of_central (t : 𝟭 CA' ≅ 𝟭 CA')
    (hhex : ∀ N : CR, Lf'.map (βg.hom.app N) ≫ βf'.hom.app (Db.obj N) ≫
        ΦA'.map (egr.hom.app N ≫ efr.inv.app N) =
      eg.hom.app (ΦR.obj N) ≫ ef.inv.app (ΦR.obj N) ≫ Lg'.map (βf.hom.app N) ≫
        βg'.hom.app (Da.obj N) ≫ ΦA'.map (t.hom.app (Db'.obj (Da.obj N))))
    {M : CA} {M' : CA'} (φ : Db'.obj M ⟶ M')
    [IsIso (Lg.map (transportUnit adja adjf ΦR ΦA βf M))]
    [IsIso (transportUnit adja' adjf' ΦR' ΦA' βf' M')] [ΦR'.ReflectsIsomorphisms] :
    IsIso (map adjf adjf' eg ef (ΦA.obj M) ≫ Rf'.map (βg'.hom.app M ≫ ΦA'.map φ)) ↔
      IsIso (map adja adja' egr efr M ≫ ra'.map φ) := by
  have key := map_transport_of_central adja adja' egr efr adjf adjf' eg ef ΦR ΦA ΦR' ΦA' βf βf'
    βg βg' t hhex M
  have hn := transportUnit_naturality adja' adjf' ΦR' ΦA' βf' φ
  have ht : ΦA'.map (t.inv.app (Db'.obj M)) ≫ ΦA'.map φ = ΦA'.map φ ≫ ΦA'.map (t.inv.app M') := by
    rw [← ΦA'.map_comp, ← ΦA'.map_comp]
    exact congrArg ΦA'.map (t.inv.naturality φ).symm
  have e : map adjf adjf' eg ef (ΦA.obj M) ≫ Rf'.map (βg'.hom.app M ≫ ΦA'.map φ) =
      inv (Lg.map (transportUnit adja adjf ΦR ΦA βf M)) ≫ βg.hom.app (ra.obj M) ≫
        ΦR'.map (map adja adja' egr efr M ≫ ra'.map φ) ≫
        transportUnit adja' adjf' ΦR' ΦA' βf' M' ≫ Rf'.map (ΦA'.map (t.inv.app M')) := by
    rw [← cancel_epi (Lg.map (transportUnit adja adjf ΦR ΦA βf M)), reassoc_of% key,
      IsIso.hom_inv_id_assoc, ΦR'.map_comp, Category.assoc, reassoc_of% hn]
    simp only [Category.assoc, ← Rf'.map_comp, Iso.inv_hom_id_app_assoc]
    rw [ht]
  rw [e]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff, isIso_iff_of_reflects_iso _ ΦR']

end Square

section Unit

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*} [Category A] [Category B]
  [Category A'] [Category B'] {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- A morphism of functors `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` is determined by its composites with `Lg` of
the unit of `Lf ⊣ Rf`. -/
theorem app_eq_app_of_unit (τ τ' : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')
    (h : ∀ N : A, Lg.map (adjf.unit.app N) ≫ τ.app (Lf.obj N) =
      Lg.map (adjf.unit.app N) ≫ τ'.app (Lf.obj N)) (K : B) :
    τ.app K = τ'.app K := by
  have key : ∀ σ : Rf ⋙ Lg ⟶ Lg' ⋙ Rf', σ.app K =
      Lg.map (adjf.unit.app (Rf.obj K)) ≫ σ.app (Lf.obj (Rf.obj K)) ≫
        Rf'.map (Lg'.map (adjf.counit.app K)) := by
    intro σ
    have hn : Lg.map (Rf.map (adjf.counit.app K)) ≫ σ.app K =
        σ.app (Lf.obj (Rf.obj K)) ≫ Rf'.map (Lg'.map (adjf.counit.app K)) :=
      σ.naturality (adjf.counit.app K)
    rw [← hn, ← Category.assoc, ← Lg.map_comp, Adjunction.right_triangle_components]
    exact (congrArg (· ≫ σ.app K) (Lg.map_id _)).trans (Category.id_comp _) |>.symm
  rw [key τ, key τ', reassoc_of% (h (Rf.obj K))]

/-- **The unit characterization of the base change map.**  A morphism of functors
`τ : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` such that `Lg` of the unit of `Lf ⊣ Rf` followed by `τ` is the unit of
`Lf' ⊣ Rf'` followed by `Rf'` of the comparison of the two composites is the base change map. -/
theorem app_eq_map_of_unit (τ : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')
    (h : ∀ N : A, Lg.map (adjf.unit.app N) ≫ τ.app (Lf.obj N) =
      adjf'.unit.app (Lg.obj N) ≫ Rf'.map (eg.hom.app N ≫ ef.inv.app N)) (K : B) :
    τ.app K = map adjf adjf' eg ef K :=
  app_eq_app_of_unit adjf τ (twoSquare adjf adjf' eg ef) (fun N => (h N).trans
    (unit_mateEquiv adjf adjf' (pullbackComparison eg ef) N).symm) K

end Unit

end Stacks.CategoryTheory.BaseChange

end
